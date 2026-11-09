import Flapjack.Compiler.Backend.FlatProps.EvaluateList
import Flapjack.Compiler.Backend.FlatProps.DoAppClock
import Flapjack.Compiler.Backend.FlatProps.PatternMatch

/-! Clock-extension preservation for the faithful flat evaluator. The private
helpers below structure the well-founded mutual induction and have no separate
HOL declarations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
/-- Flapjack proof infrastructure: Clock changes preserve the row chosen by the evaluator. -/
private theorem selectRowClock {C F : Type} (state : State C F)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (value noMatch : Value) (clock : Nat) :
    selectRow { state with clock := clock } rows value noMatch = selectRow state rows value noMatch := by
  simp only [selectRow, pmatchRows_ignoreClock]

/-- Flapjack proof infrastructure: Clock addition commutes with a positive clock decrement. -/
private theorem decClockAdd {C F : Type} (state : State C F) (extra : Nat) (positive : state.clock ≠ 0) :
    decClock { state with clock := state.clock + extra } =
      { decClock state with clock := (decClock state).clock + extra } := by
  simp only [decClock]
  congr 1
  omega

/-- Flapjack proof infrastructure: Expose the matching case through the evaluator row-selection helper. -/
private theorem matEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.mat trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => match selectRow next rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
        | .error error => (next, .err error)
        | .ok (bindings, branch) => evaluate { env with v := bindings ++ env.v } next [branch] := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    simp only [headValue_eq_holHd]
    cases selectRow next rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV <;> rfl

/-- Flapjack proof infrastructure: Expose the handler case through the evaluator row-selection helper. -/
private theorem handleEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    evaluate env state [.handle trace body rows] =
      match fixClock state (evaluate env state [body]) with
      | (next, .err (.raise value)) => match selectRow next rows value value with
        | .error error => (next, .err error)
        | .ok (bindings, branch) => evaluate { env with v := bindings ++ env.v } next [branch]
      | (next, result) => (next, result) := by
  rw [evaluate]
  generalize fixClock state (evaluate env state [body]) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | val values => rfl
  | err error =>
    cases error with
    | abort abort => rfl
    | raise value =>
      dsimp only
      cases selectRow next rows value value <;> simp

/-- Flapjack proof infrastructure: The lifted primitive result commutes with clock addition. -/
private theorem applyResultAddClock {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) (extra : Nat) :
    applyResult { state with clock := state.clock + extra } op values =
      ({ (applyResult state op values).1 with clock := (applyResult state op values).1.clock + extra },
        (applyResult state op values).2) := by
  cases run : doApp state op values with
  | none =>
    have shifted := doApp_addToClock_none state op values extra run
    simp [applyResult, run, shifted]
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have shifted := doApp_addToClock state op values next result extra run
    cases result <;> simp [applyResult, run, shifted]

/-- Flapjack proof infrastructure: Expose the evaluator clause for non-special primitive operations. -/
private theorem appOtherEquation {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk)) :
    evaluate env state [.app trace op args] =
      match fixClock state (evaluate env state args.reverse) with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => applyResult next op values.reverse := by
  rw [evaluate]
  generalize fixClock state (evaluate env state args.reverse) = result
  obtain ⟨next, result⟩ := result
  cases result with
  | err error => rfl
  | val values =>
    cases op with
    | src source => cases source <;> simp_all [applyResult]
    | globalVarAlloc n | globalVarInit n | globalVarLookup n | el n => rfl
    | tagLenEq n m => rfl
    | lenEq n => rfl
    | id => rfl

private def nonTimeout {α : Type} (result : Result α Value) : Prop :=
  result ≠ .err (.abort .timeoutError)
/-- Flapjack proof infrastructure: The list sequencing induction case preserves clock shifts. -/
private theorem evalConsShift {C F : Type} (env : Environment Value) (state : State C F)
    (e : FlatLang.Exp) (es : List FlatLang.Exp) (extra : Nat)
    (headIH : ∀ (next : State C F) result,
      evaluate env state [e] = (next, result) ∧ nonTimeout result →
      evaluate env { state with clock := state.clock + extra } [e] = ({ next with clock := next.clock + extra }, result))
    (tailIH : ∀ (s next : State C F) result, s.clock ≤ state.clock →
      evaluate env s es = (next, result) ∧ nonTimeout result →
      evaluate env { s with clock := s.clock + extra } es = ({ next with clock := next.clock + extra }, result))
    (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state (e :: es) = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } (e :: es) =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases head : evaluate env state [e] with
  | mk middle headResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state [e]
      simpa [head] using bound
    cases headResult with
    | err error =>
      simp [evaluate_cons, head] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := headIH middle (.err error) ⟨head, safe⟩
      simp [evaluate_cons, shifted] 
    | val values =>
      cases tail : evaluate env middle es with
      | mk last tailResult =>
        cases tailResult with
        | err error =>
          simp [evaluate_cons, head, tail] at run
          rcases run with ⟨rfl, rfl⟩
          have shiftedHead := headIH middle (.val values) ⟨head, by simp [nonTimeout]⟩
          have shiftedTail := tailIH middle last (.err error) bound ⟨tail, safe⟩
          simp [evaluate_cons, shiftedHead, shiftedTail]
        | val values' =>
          simp [evaluate_cons, head, tail] at run
          rcases run with ⟨rfl, rfl⟩
          have shiftedHead := headIH middle (.val values) ⟨head, by simp [nonTimeout]⟩
          have shiftedTail := tailIH middle last (.val values') bound ⟨tail, by simp [nonTimeout]⟩
          simp [evaluate_cons, shiftedHead, shiftedTail]
/-- Flapjack proof infrastructure: The multi-expression induction case uses strictly smaller expression lists. -/
private theorem evalManyShift {C F : Type} (env : Environment Value) (state : State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp) (extra : Nat)
    (ih : ∀ (env' : Environment Value) (s : State C F) (es : List FlatLang.Exp),
      s.clock ≤ state.clock → expsWeight es < expsWeight (first :: second :: rest) →
      ∀ (next : State C F) result, evaluate env' s es = (next, result) ∧ nonTimeout result →
        evaluate env' { s with clock := s.clock + extra } es = ({ next with clock := next.clock + extra }, result))
    (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state (first :: second :: rest) = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } (first :: second :: rest) =
      ({ next with clock := next.clock + extra }, result) := by
  apply evalConsShift env state first (second :: rest) extra
  · intro next result h
    apply ih env state [first] (by omega) ?_ next result h
    simp only [expsWeight]
    have := expWeight_pos second
    omega
  · intro s next result hclock h
    apply ih env s (second :: rest) hclock ?_ next result h
    simp only [expsWeight]
    omega
  · exact premises
private def exprShift {C F : Type} (extra : Nat) (env : Environment Value)
    (state : State C F) (es : List FlatLang.Exp) : Prop :=
  ∀ (next : State C F) (result : Result (List Value) Value),
    evaluate env state es = (next, result) ∧ nonTimeout result →
      evaluate env { state with clock := state.clock + extra } es =
        ({ next with clock := next.clock + extra }, result)

private def decsShift {C F : Type} (extra : Nat) (state : State C F) (ds : List FlatLang.Exp) : Prop :=
  ∀ (next : State C F) (result : Option (ErrorResult Value)),
    evaluateDecs state ds = (next, result) ∧ result ≠ some (.abort .timeoutError) →
      evaluateDecs { state with clock := state.clock + extra } ds =
        ({ next with clock := next.clock + extra }, result)

/-- Flapjack proof infrastructure: The ordinary-primitive application induction case preserves clock shifts. -/
private theorem appOtherShift {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (extra : Nat) (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (argsIH : exprShift extra env state args.reverse) (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state [.app trace op args] = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } [.app trace op args] =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases child : evaluate env state args.reverse with
  | mk middle childResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state args.reverse
      simpa [child] using bound
    have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
    cases childResult with
    | err error =>
      simp [appOtherEquation env state trace op args notCall notEval notForce, fixClock, Nat.min_eq_right bound, child] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := argsIH middle (.err error) ⟨child, safe⟩
      simp [appOtherEquation env _ trace op args notCall notEval notForce, fixClock, Nat.min_eq_right shiftedBound, shifted]
    | val values =>
      simp only [appOtherEquation env state trace op args notCall notEval notForce, fixClock,
        Nat.min_eq_right bound, child] at run
      have shifted := argsIH middle (.val values) ⟨child, by simp [nonTimeout]⟩
      simp only [appOtherEquation env _ trace op args notCall notEval notForce, fixClock,
        Nat.min_eq_right shiftedBound, shifted]
      have primitive := applyResultAddClock middle op values.reverse extra
      simpa only [run] using primitive

/-- Flapjack proof infrastructure: The function-call induction case uses the smaller-clock hypothesis. -/
private theorem appCallShift {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : exprShift extra env state args.reverse)
    (bodyIH : ∀ (env' : Environment Value) (s : State C F) (body : FlatLang.Exp),
      s.clock < state.clock → exprShift extra env' s [body])
    (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state [.app trace (.src .opapp) args] = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } [.app trace (.src .opapp) args] =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases child : evaluate env state args.reverse with
  | mk middle childResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state args.reverse
      simpa [child] using bound
    have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
    cases childResult with
    | err error =>
      simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := argsIH middle (.err error) ⟨child, safe⟩
      simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted]
    | val values =>
      have shifted := argsIH middle (.val values) ⟨child, by simp [nonTimeout]⟩
      cases call : doOpApp values.reverse with
      | none =>
        simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, call] at run
        rcases run with ⟨rfl, rfl⟩
        simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, call]
      | some pair =>
        obtain ⟨newEnv, body⟩ := pair
        by_cases zero : middle.clock = 0
        · simp [evaluate_app_source, fixClock, child, call, zero] at run
          rcases run with ⟨rfl, rfl⟩
          exact (safe rfl).elim
        · have decrease : (decClock middle).clock < state.clock := by simp [decClock]; omega
          have ih := bodyIH newEnv (decClock middle) body decrease
          simp only [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, call, zero, ↓reduceIte] at run
          have shiftedBody := ih next result ⟨run, safe⟩
          have nonzero : middle.clock + extra ≠ 0 := by omega
          simpa only [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, call,
            nonzero, ↓reduceIte, decClockAdd middle extra zero] using shiftedBody

/-- Flapjack proof infrastructure: The dynamic-evaluation induction case uses the smaller-clock declaration hypothesis. -/
private theorem appEvalShift {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : exprShift extra env state args.reverse)
    (decsIH : ∀ (s : State C F) (ds : List FlatLang.Exp),
      s.clock < state.clock → decsShift extra s ds)
    (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state [.app trace (.src .eval) args] = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } [.app trace (.src .eval) args] =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases child : evaluate env state args.reverse with
  | mk middle childResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state args.reverse
      simpa [child] using bound
    have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
    cases childResult with
    | err error =>
      simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := argsIH middle (.err error) ⟨child, safe⟩
      simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted]
    | val values =>
      have shifted := argsIH middle (.val values) ⟨child, by simp [nonTimeout]⟩
      cases decoded : doEval values.reverse middle.evalConfig with
      | none =>
        simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, decoded]
      | some payload =>
        obtain ⟨decs, config, returnValue⟩ := payload
        by_cases zero : middle.clock = 0
        · simp [evaluate_app_source, fixClock, child, decoded, zero] at run
          rcases run with ⟨rfl, rfl⟩
          exact (safe rfl).elim
        · have decrease : (decClock { middle with evalConfig := config }).clock < state.clock := by simp [decClock]; omega
          have ih := decsIH (decClock { middle with evalConfig := config }) decs decrease
          cases decResult : evaluateDecs (decClock { middle with evalConfig := config }) decs with
          | mk last error =>
            cases error with
            | none =>
              simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, decoded, zero, decResult] at run
              rcases run with ⟨rfl, rfl⟩
              have shiftedDecs := ih last none ⟨decResult, by simp⟩
              simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, decoded,
                decClockAdd { middle with evalConfig := config } extra zero, shiftedDecs] <;> omega
            | some error =>
              simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, decoded, zero, decResult] at run
              rcases run with ⟨rfl, rfl⟩
              have shiftedDecs := ih last (some error) ⟨decResult, by simpa [nonTimeout] using safe⟩
              simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, decoded,
                decClockAdd { middle with evalConfig := config } extra zero, shiftedDecs] <;> omega

/-- Flapjack proof infrastructure: The thunk-forcing induction case uses the smaller-expression hypothesis. -/
private theorem appForceShift {C F : Type} (env : Environment Value) (state : State C F)
    (trace : Flapjack.Compiler.Backend.BackendCommon.Tra) (args : List FlatLang.Exp) (extra : Nat)
    (argsIH : exprShift extra env state args.reverse)
    (forceIH : ∀ (s : State C F) (value : Value), s.clock ≤ state.clock →
      exprShift extra ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ s
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))])
    (next : State C F) (result : Result (List Value) Value)
    (premises : evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args] = (next, result) ∧ nonTimeout result) :
    evaluate env { state with clock := state.clock + extra } [.app trace (.src (.thunkOp .forceThunk)) args] =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases child : evaluate env state args.reverse with
  | mk middle childResult =>
    have bound : middle.clock ≤ state.clock := by
      have bound := evaluate_clock_mutual.1 env state args.reverse
      simpa [child] using bound
    have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
    cases childResult with
    | err error =>
      simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := argsIH middle (.err error) ⟨child, safe⟩
      simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted]
    | val values =>
      have shifted := argsIH middle (.val values) ⟨child, by simp [nonTimeout]⟩
      cases dest : destThunk values middle.refs with
      | badRef | notThunk =>
        simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, dest] at run
        rcases run with ⟨rfl, rfl⟩
        simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, dest]
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, dest] at run
          rcases run with ⟨rfl, rfl⟩
          simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, dest]
        | notEvaluated =>
          let name := Flapjack.Basis.Pure.MlString.ofString "f"
          cases bodyRun : evaluate ⟨[(name, value)]⟩ middle [appUnit (.varLocal .none name)] with
          | mk last bodyResult =>
            dsimp only [name] at bodyRun
            cases bodyResult with
            | err error =>
              simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, dest, bodyRun] at run
              rcases run with ⟨rfl, rfl⟩
              have shiftedBody := forceIH middle value bound last (.err error) ⟨bodyRun, safe⟩
              simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, dest, shiftedBody]
            | val results =>
              have shiftedBody := forceIH middle value bound last (.val results) ⟨bodyRun, by simp [nonTimeout]⟩
              cases updated : updateThunk values last.refs results with
              | none =>
                simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, dest, bodyRun, updated] at run
                rcases run with ⟨rfl, rfl⟩
                simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, dest, shiftedBody, updated]
              | some refs =>
                simp [evaluate_app_source, fixClock, Nat.min_eq_right bound, child, dest, bodyRun, updated] at run
                rcases run with ⟨rfl, rfl⟩
                simp [evaluate_app_source, fixClock, Nat.min_eq_right shiftedBound, shifted, dest, shiftedBody, updated]

/-- Flapjack proof infrastructure: Mutual clock-and-weight induction for expressions and declaration lists. -/
private theorem exprDecsShift {C F : Type} (extra : Nat) :
    (∀ (env : Environment Value) (state : State C F) es, exprShift extra env state es) ∧
    (∀ (state : State C F) ds, decsShift extra state ds) := by
  apply flatEvaluateMeasureRec
  · intro env state es exprIH smallerE decIH smallerD
    cases es with
    | nil =>
      intro next result premises
      obtain ⟨run, safe⟩ := premises
      simp [evaluate_nil_source] at run
      rcases run with ⟨rfl, rfl⟩
      exact evaluate_nil_source _ _
    | cons first rest =>
      cases rest with
      | nil =>
        intro next result premises
        cases first with
        | lit trace literal =>
          obtain ⟨run, _⟩ := premises
          simp [evaluate_lit_source] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluate_lit_source _ _ _ _
        | fn trace name body =>
          obtain ⟨run, _⟩ := premises
          simp [evaluate_fn_source] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluate_fn_source _ _ _ _ _
        | varLocal trace name =>
          obtain ⟨run, _⟩ := premises
          rw [evaluate_varLocal_source] at run ⊢
          cases found : env.v.lookup name <;> simp_all
        | raise trace body =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          cases child : evaluate env state [body] with
          | mk middle childResult =>
            cases childResult with
            | err error =>
              simp [evaluate_raise_source, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.err error) ⟨child, safe⟩
              simp [evaluate_raise_source, shifted]
            | val values =>
              simp [evaluate_raise_source, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              simp [evaluate_raise_source, shifted]
        | con trace constructor args =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state args.reverse (by omega) (by
            rw [expsWeight_reverse]
            simp only [expsWeight, expWeight]
            omega)
          cases child : evaluate env state args.reverse with
          | mk middle childResult =>
            cases childResult with
            | err error =>
              simp [evaluate_con_source, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.err error) ⟨child, safe⟩
              simp [evaluate_con_source, shifted]
            | val values =>
              simp [evaluate_con_source, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              simp [evaluate_con_source, shifted]
        | letrec trace funs body =>
          obtain ⟨run, safe⟩ := premises
          by_cases distinct : (funs.map Prod.fst).Nodup
          · simp only [evaluate_letrec_source, distinct, ↓reduceIte] at run ⊢
            exact exprIH _ state [body] (by omega) (by simp only [expsWeight, expWeight]; omega) next result ⟨run, safe⟩
          · simp [evaluate_letrec_source, distinct] at run ⊢
            rcases run with ⟨rfl, rfl⟩
            simp
        | if_ trace condition yes no =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state [condition] (by omega) (by simp only [expsWeight, expWeight]; omega)
          cases child : evaluate env state [condition] with
          | mk middle childResult =>
            have bound : middle.clock ≤ state.clock := by
              have bound := evaluate_clock_mutual.1 env state [condition]
              simpa [child] using bound
            have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
            cases childResult with
            | err error =>
              simp [evaluate_if_source, fixClock, Nat.min_eq_right bound, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.err error) ⟨child, safe⟩
              simp [evaluate_if_source, fixClock, Nat.min_eq_right shiftedBound, shifted]
            | val values =>
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              cases chosen : doIf (@Flapjack.holHd Value ⟨unitValue⟩ values) yes no with
              | none =>
                simp [evaluate_if_source, fixClock, Nat.min_eq_right bound, child, chosen] at run
                rcases run with ⟨rfl, rfl⟩
                simp [evaluate_if_source, fixClock, Nat.min_eq_right shiftedBound, shifted, chosen]
              | some branch =>
                have branchWeight : expsWeight [branch] < expsWeight [.if_ trace condition yes no] := by
                  have select := doIf_either_or _ yes no branch chosen
                  rcases select with rfl | rfl <;> simp only [expsWeight, expWeight] <;> omega
                have branchIH := exprIH env middle [branch] bound branchWeight
                simp only [evaluate_if_source, fixClock, Nat.min_eq_right bound, child, chosen] at run
                have shiftedBranch := branchIH next result ⟨run, safe⟩
                simpa only [evaluate_if_source, fixClock, Nat.min_eq_right shiftedBound, shifted, chosen] using shiftedBranch
        | let_ trace name first body =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state [first] (by omega) (by simp only [expsWeight, expWeight]; omega)
          cases child : evaluate env state [first] with
          | mk middle childResult =>
            have bound : middle.clock ≤ state.clock := by
              have bound := evaluate_clock_mutual.1 env state [first]
              simpa [child] using bound
            have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
            cases childResult with
            | err error =>
              simp [evaluate_let_source, fixClock, Nat.min_eq_right bound, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.err error) ⟨child, safe⟩
              simp [evaluate_let_source, fixClock, Nat.min_eq_right shiftedBound, shifted]
            | val values =>
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              simp only [evaluate_let_source, fixClock, Nat.min_eq_right bound, child] at run
              cases name with
              | none =>
                have bodyIH := exprIH env middle [body] bound (by simp only [expsWeight, expWeight]; omega)
                have shiftedBody := bodyIH next result ⟨run, safe⟩
                simpa only [evaluate_let_source, fixClock, Nat.min_eq_right shiftedBound, shifted] using shiftedBody
              | some n =>
                have bodyIH := exprIH { env with v := (n, @Flapjack.holHd Value ⟨unitValue⟩ values) :: env.v }
                  middle [body] bound (by simp only [expsWeight, expWeight]; omega)
                have shiftedBody := bodyIH next result ⟨run, safe⟩
                simpa only [evaluate_let_source, fixClock, Nat.min_eq_right shiftedBound, shifted] using shiftedBody
        | mat trace body rows =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          cases child : evaluate env state [body] with
          | mk middle childResult =>
            have bound : middle.clock ≤ state.clock := by
              have bound := evaluate_clock_mutual.1 env state [body]
              simpa [child] using bound
            have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
            cases childResult with
            | err error =>
              simp [matEquation, fixClock, Nat.min_eq_right bound, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.err error) ⟨child, safe⟩
              simp [matEquation, fixClock, Nat.min_eq_right shiftedBound, shifted]
            | val values =>
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              cases selected : selectRow middle rows (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV with
              | error error =>
                simp [matEquation, fixClock, Nat.min_eq_right bound, child, selected] at run
                rcases run with ⟨rfl, rfl⟩
                simp [matEquation, fixClock, Nat.min_eq_right shiftedBound, shifted, selectRowClock, selected]
              | ok pair =>
                obtain ⟨bindings, branch⟩ := pair
                have weight := selectRow_weight rows middle (@Flapjack.holHd Value ⟨unitValue⟩ values) bindExnV bindings branch selected
                have branchIH := exprIH { env with v := bindings ++ env.v } middle [branch] bound
                  (by simp only [expsWeight, expWeight]; omega)
                simp only [matEquation, fixClock, Nat.min_eq_right bound, child, selected] at run
                have shiftedBranch := branchIH next result ⟨run, safe⟩
                simpa only [matEquation, fixClock, Nat.min_eq_right shiftedBound, shifted, selectRowClock, selected] using shiftedBranch
        | handle trace body rows =>
          obtain ⟨run, safe⟩ := premises
          have ih := exprIH env state [body] (by omega) (by simp only [expsWeight, expWeight]; omega)
          cases child : evaluate env state [body] with
          | mk middle childResult =>
            have bound : middle.clock ≤ state.clock := by
              have bound := evaluate_clock_mutual.1 env state [body]
              simpa [child] using bound
            have shiftedBound : middle.clock + extra ≤ state.clock + extra := by omega
            cases childResult with
            | val values =>
              simp [handleEquation, fixClock, Nat.min_eq_right bound, child] at run
              rcases run with ⟨rfl, rfl⟩
              have shifted := ih middle (.val values) ⟨child, by simp [nonTimeout]⟩
              simp [handleEquation, fixClock, Nat.min_eq_right shiftedBound, shifted]
            | err error =>
              cases error with
              | abort abort =>
                simp [handleEquation, fixClock, Nat.min_eq_right bound, child] at run
                rcases run with ⟨rfl, rfl⟩
                have shifted := ih middle (.err (.abort abort)) ⟨child, safe⟩
                simp [handleEquation, fixClock, Nat.min_eq_right shiftedBound, shifted]
              | raise value =>
                have shifted := ih middle (.err (.raise value)) ⟨child, by simp [nonTimeout]⟩
                cases selected : selectRow middle rows value value with
                | error error =>
                  simp [handleEquation, fixClock, Nat.min_eq_right bound, child, selected] at run
                  rcases run with ⟨rfl, rfl⟩
                  simp [handleEquation, fixClock, Nat.min_eq_right shiftedBound, shifted, selectRowClock, selected]
                | ok pair =>
                  obtain ⟨bindings, branch⟩ := pair
                  have weight := selectRow_weight rows middle value value bindings branch selected
                  have branchIH := exprIH { env with v := bindings ++ env.v } middle [branch] bound
                    (by simp only [expsWeight, expWeight]; omega)
                  simp only [handleEquation, fixClock, Nat.min_eq_right bound, child, selected] at run
                  have shiftedBranch := branchIH next result ⟨run, safe⟩
                  simpa only [handleEquation, fixClock, Nat.min_eq_right shiftedBound, shifted, selectRowClock, selected] using shiftedBranch
        | app trace op args =>
          have argsIH := exprIH env state args.reverse (by omega) (by
            rw [expsWeight_reverse]
            simp only [expsWeight, expWeight]
            omega)
          by_cases call : op = .src .opapp
          · subst op
            apply appCallShift env state trace args extra argsIH ?_ next result premises
            intro env' s body smaller
            exact smallerE env' s [body] smaller
          · by_cases dynamic : op = .src .eval
            · subst op
              apply appEvalShift env state trace args extra argsIH ?_ next result premises
              intro s ds smaller
              exact smallerD s ds smaller
            · by_cases force : op = .src (.thunkOp .forceThunk)
              · subst op
                apply appForceShift env state trace args extra argsIH ?_ next result premises
                intro s value hclock
                apply exprIH _ s _ hclock
                have weight := appUnit_force_weight trace args
                simp only [expsWeight]
                omega
              · exact appOtherShift env state trace op args extra call dynamic force argsIH next result premises
      | cons second rest =>
        intro next result premises
        apply evalManyShift env state first second rest extra ?_ next result premises
        intro env' state' es' hclock hweight
        exact exprIH env' state' es' hclock hweight
  · intro state ds exprIH smallerE decIH smallerD
    cases ds with
    | nil =>
      intro next result premises
      obtain ⟨run, safe⟩ := premises
      simp [evaluateDecs] at run
      rcases run with ⟨rfl, rfl⟩
      simp [evaluateDecs]
    | cons first rest =>
      intro next result premises
      obtain ⟨run, safe⟩ := premises
      have headIH := exprIH ⟨[]⟩ state [first] (by omega) (by simp only [expsWeight]; omega)
      cases child : evaluate ⟨[]⟩ state [first] with
      | mk middle childResult =>
        have bound : middle.clock ≤ state.clock := by
          have bound := evaluate_clock_mutual.1 ⟨[]⟩ state [first]
          simpa [child] using bound
        cases childResult with
        | err error =>
          simp [evaluateDecs_cons, evaluateDec_source, child] at run
          rcases run with ⟨rfl, rfl⟩
          have shifted := headIH middle (.err error) ⟨child, by simpa [nonTimeout] using safe⟩
          simp [evaluateDecs_cons, evaluateDec_source, shifted]
        | val values =>
          have shifted := headIH middle (.val values) ⟨child, by simp [nonTimeout]⟩
          by_cases unit : values = [unitValue]
          · simp [evaluateDecs_cons, evaluateDec_source, child, unit] at run
            have restIH := decIH middle rest bound (by simp only [expsWeight]; have := expWeight_pos first; omega)
            have shiftedRest := restIH next result ⟨run, safe⟩
            simpa [evaluateDecs_cons, evaluateDec_source, shifted, unit] using shiftedRest
          · simp [evaluateDecs_cons, evaluateDec_source, child, unit] at run
            rcases run with ⟨rfl, rfl⟩
            simp [evaluateDecs_cons, evaluateDec_source, shifted, unit]

/-- Flapjack proof infrastructure: The single-declaration projection follows from expression clock shifting. -/
private theorem decShift {C F : Type} (extra : Nat) (state : State C F) (declaration : FlatLang.Exp)
    (next : State C F) (result : Option (ErrorResult Value))
    (premises : evaluateDec state declaration = (next, result) ∧ result ≠ some (.abort .timeoutError)) :
    evaluateDec { state with clock := state.clock + extra } declaration =
      ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨run, safe⟩ := premises
  cases child : evaluate ⟨[]⟩ state [declaration] with
  | mk middle childResult =>
    cases childResult with
    | err error =>
      simp [evaluateDec_source, child] at run
      rcases run with ⟨rfl, rfl⟩
      have shifted := (exprDecsShift extra).1 ⟨[]⟩ state [declaration] middle (.err error)
        ⟨child, by simpa [nonTimeout] using safe⟩
      simp [evaluateDec_source, shifted]
    | val values =>
      have shifted := (exprDecsShift extra).1 ⟨[]⟩ state [declaration] middle (.val values)
        ⟨child, by simp [nonTimeout]⟩
      by_cases unit : values = [unitValue]
      · simp [evaluateDec_source, child, unit] at run
        rcases run with ⟨rfl, rfl⟩
        simp [evaluateDec_source, shifted, unit]
      · simp [evaluateDec_source, child, unit] at run
        rcases run with ⟨rfl, rfl⟩
        simp [evaluateDec_source, shifted, unit]

/-- Increasing the clock preserves every non-timeout flat evaluation result. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_add_to_clock"]
theorem evaluate_addToClock {C F : Type} (extra : Nat) :
    (∀ (env : Environment Value) (state : State C F) (es : List FlatLang.Exp)
      (next : State C F) (result : Result (List Value) Value),
      evaluate env state es = (next, result) ∧ result ≠ .err (.abort .timeoutError) →
        evaluate env { state with clock := state.clock + extra } es =
          ({ next with clock := next.clock + extra }, result)) ∧
    (∀ (state : State C F) (declaration : FlatLang.Exp) (next : State C F)
      (result : Option (ErrorResult Value)),
      evaluateDec state declaration = (next, result) ∧ result ≠ some (.abort .timeoutError) →
        evaluateDec { state with clock := state.clock + extra } declaration =
          ({ next with clock := next.clock + extra }, result)) ∧
    (∀ (state : State C F) (ds : List FlatLang.Exp) (next : State C F)
      (result : Option (ErrorResult Value)),
      evaluateDecs state ds = (next, result) ∧ result ≠ some (.abort .timeoutError) →
        evaluateDecs { state with clock := state.clock + extra } ds =
          ({ next with clock := next.clock + extra }, result)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env state es next result premises
    exact (exprDecsShift extra).1 env state es next result premises
  · intro state declaration next result premises
    exact decShift extra state declaration next result premises
  · intro state ds next result premises
    exact (exprDecsShift extra).2 state ds next result premises

/-- The declaration-list clock-shift consequence in the original premise order. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_add_to_clock"]
theorem evaluateDecs_addToClock {C F : Type} (extra : Nat) :
    ∀ (ds : List FlatLang.Exp) (state next : State C F) (result : Option (ErrorResult Value)),
      result ≠ some (.abort .timeoutError) ∧ evaluateDecs state ds = (next, result) →
        evaluateDecs { state with clock := state.clock + extra } ds =
          ({ next with clock := next.clock + extra }, result) := by
  intro ds state next result premises
  exact (evaluate_addToClock extra).2.2 state ds next result ⟨premises.2, premises.1⟩

end Flapjack.Compiler.Backend.FlatProps
