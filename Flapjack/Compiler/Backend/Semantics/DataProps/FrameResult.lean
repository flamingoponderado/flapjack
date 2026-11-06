import Flapjack.Compiler.Backend.Semantics.DataProps.FrameSize
import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveLocals

/-! Result-sensitive frame-size invariants for data evaluation. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Continuing execution preserves the entry frame size; a raised exception
uses the frame size selected by the entry exception jump. This auxiliary
predicate has no direct HOL declaration. -/
def frameSizeResult {C F : Type} (source : State C F)
    (result : Option (Result (List Value) Value)) (next : State C F) : Prop :=
  match result with
  | none => next.localsSize = source.localsSize
  | some (.err (.raise _)) => ∃ jumped, jumpExc source = some jumped ∧ next.localsSize = jumped.localsSize
  | _ => True

/-- The frame-size invariant composes across sequential evaluation. -/
theorem evaluate_seq_frameSizeResult {C F : Type} (first second : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (firstIH : ∀ after : State C F, ∀ outcome,
      evaluate first state = (outcome, after) → frameSizeResult state outcome after)
    (secondIH : ∀ before after : State C F, ∀ outcome,
      before.clock ≤ state.clock → evaluate second before = (outcome, after) → frameSizeResult before outcome after)
    (run : evaluate (.seq first second) state = (result, next)) : frameSizeResult state result next := by
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    rw [firstRun] at run
    have firstSize := firstIH mid outcome firstRun
    cases outcome with
    | some stopped =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact firstSize
    | none =>
      have midSize : mid.localsSize = state.localsSize := firstSize
      have midControl := evaluate_stackResult first state mid none firstRun
      have midClock : mid.clock ≤ state.clock := by
        have bound := evaluate_clock_le first state
        simpa [firstRun] using bound
      have secondSize := secondIH mid next result midClock run
      cases result with
      | none => exact secondSize.trans midSize
      | some stopped =>
        cases stopped with
        | val values => trivial
        | err error =>
          cases error with
          | abort reason => trivial
          | raise value =>
            obtain ⟨jumped, jumpRun, nextSize⟩ := secondSize
            let originalJump := { state with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }
            exact ⟨originalJump, jumpExc_transport mid state jumped midControl.1.symm midControl.2.symm jumpRun, nextSize⟩

/-- The frame-size invariant composes across conditional branches. -/
theorem evaluate_if_frameSizeResult {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (yesIH : ∀ after : State C F, ∀ outcome,
      evaluate yes state = (outcome, after) → frameSizeResult state outcome after)
    (noIH : ∀ after : State C F, ∀ outcome,
      evaluate no state = (outcome, after) → frameSizeResult state outcome after)
    (run : evaluate (.ifThenElse name yes no) state = (result, next)) : frameSizeResult state result next := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read] at run; obtain ⟨rfl, rfl⟩ := run; trivial
  | some value =>
    by_cases yesTest : isBool true value
    · apply yesIH next result
      simpa [evaluate, read, yesTest] using run
    · by_cases noTest : isBool false value
      · apply noIH next result
        simpa [evaluate, read, yesTest, noTest] using run
      · simp [evaluate, read, yesTest, noTest] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

/-- A raise either reports a type error or selects the exception frame. -/
theorem evaluate_raise_frameSizeResult {C F : Type} (name : Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.raise name) state = (result, next)) : frameSizeResult state result next := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read] at run; obtain ⟨rfl, rfl⟩ := run; trivial
  | some value =>
    cases jump : jumpExc state with
    | none => simp [evaluate, read, jump] at run; obtain ⟨rfl, rfl⟩ := run; trivial
    | some jumped =>
      simp [evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨jumped, jump, rfl⟩

/-- An assignment either continues with the same frame size or aborts. -/
theorem evaluate_assign_frameSizeResult {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.assign dest op names live) state = (result, next)) : frameSizeResult state result next := by
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  · cases read : getVars names state.locals with
    | none => simp [evaluate, invalid, read] at run; obtain ⟨rfl, rfl⟩ := run; trivial
    | some args =>
      cases cut : cutStateOpt live state with
      | none => simp [evaluate, invalid, read, cut] at run; obtain ⟨rfl, rfl⟩ := run; trivial
      | some prepared =>
        have cutSize : prepared.localsSize = state.localsSize := by
          cases live with
          | none => simp [cutStateOpt] at cut; subst prepared; rfl
          | some live =>
            simp only [cutStateOpt, cutState] at cut
            cases found : cutEnv live state.locals <;> simp [found] at cut
            subst prepared
            rfl
        cases app : doApp op args prepared with
        | err error =>
          cases error with
          | raise value => exact False.elim (doApp_ne_raise op args prepared value app)
          | abort reason =>
            simp [evaluate, invalid, read, cut, app] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          have control := doApp_control op args prepared applied value app
          simp [evaluate, invalid, read, cut, app] at run
          obtain ⟨rfl, rfl⟩ := run
          simpa [frameSizeResult, setVar, installSfs] using control.2.2.2.1.trans cutSize

theorem evaluate_skip_frameSizeResult {C F : Type} (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate .skip state = (result, next)) : frameSizeResult state result next := by
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  rfl

theorem evaluate_move_frameSizeResult {C F : Type} (dest src : Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.move dest src) state = (result, next)) : frameSizeResult state result next := by
  cases read : getVar src state.locals <;> simp [evaluate, read] at run
  all_goals obtain ⟨rfl, rfl⟩ := run
  all_goals simp [frameSizeResult, setVar]

theorem evaluate_tick_frameSizeResult {C F : Type} (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate .tick state = (result, next)) : frameSizeResult state result next := by
  by_cases zero : state.clock = 0 <;> simp [evaluate, zero] at run
  all_goals obtain ⟨rfl, rfl⟩ := run
  all_goals simp [frameSizeResult, decClock]

theorem evaluate_makeSpace_frameSizeResult {C F : Type} (amount : Nat) (names : NumSet)
    (state next : State C F) (result : Option (Result (List Value) Value))
    (run : evaluate (.makeSpace amount names) state = (result, next)) : frameSizeResult state result next := by
  cases cut : cutEnv names state.locals <;> simp [evaluate, cut] at run
  all_goals obtain ⟨rfl, rfl⟩ := run
  all_goals simp [frameSizeResult, addSpace]

theorem evaluate_return_frameSizeResult {C F : Type} (names : List Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.return names) state = (result, next)) : frameSizeResult state result next := by
  cases read : getVars names state.locals <;> simp [evaluate, read] at run
  all_goals obtain ⟨rfl, rfl⟩ := run
  all_goals trivial

/-- An exception crossing an ordinary saved frame retains the frame size
selected by the caller's exception jump. -/
theorem jumpExc_callEnv_push_noHandler_inv_size {C F : Type} (state jumped : State C F)
    (env : Spt Value) (args : List Value) (size : Option Nat)
    (run : jumpExc (callEnv args size (pushEnv env false (decClock state))) = some jumped) :
    ∃ original, jumpExc state = some original ∧ jumped.localsSize = original.localsSize := by
  rw [jumpExc_callEnv_push_noHandler] at run
  cases initial : jumpExc state with
  | none => simp [initial] at run
  | some original =>
    simp [initial] at run
    subst jumped
    exact ⟨original, rfl, rfl⟩

/-- The force case of the frame-size invariant, assuming it for evaluated
thunk bodies at smaller clocks. -/
theorem evaluate_force_frameSizeResult {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state next : State C F) (result : Option (Result (List Value) Value))
    (bodyIH : ∀ (body : DataLang.Prog) (entered finished : State C F) (outcome : Option (Result (List Value) Value)),
      entered.clock < state.clock → evaluate body entered = (outcome, finished) → frameSizeResult entered outcome finished)
    (run : evaluate (.force ret label src) state = (result, next)) : frameSizeResult state result next := by
  cases result with
  | none => exact evaluate_force_normal_localsSize ret label src state next run
  | some outcome =>
    cases outcome with
    | val values => trivial
    | err error =>
      cases error with
      | abort reason => trivial
      | raise raised =>
        cases read : getVar src state.locals with
        | none => simp [evaluate, read] at run
        | some thunk =>
          cases inspect : destThunk thunk state.refs with
          | badRef => simp [evaluate, read, inspect] at run
          | notThunk => simp [evaluate, read, inspect] at run
          | isThunk mode value =>
            cases mode with
            | evaluated =>
              cases ret with
              | none => simp [evaluate, read, inspect] at run
              | some pair =>
                obtain ⟨dest, names⟩ := pair
                cases cut : cutEnv names state.locals <;> simp [evaluate, read, inspect, cut] at run
            | notEvaluated =>
              cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
              | none => simp [evaluate, read, inspect, found] at run
              | some triple =>
                obtain ⟨args, body, size⟩ := triple
                cases ret with
                | none =>
                  by_cases zero : state.clock = 0
                  · simp [evaluate, read, inspect, found, zero] at run
                  · let entered := callEnv args size (decClock state)
                    have smaller : entered.clock < state.clock := by simp [entered, callEnv, decClock]; omega
                    have bodyRun : evaluate body entered = (some (.err (.raise raised)), next) := by
                      cases called : evaluate body entered with
                      | mk outcome last =>
                        cases outcome <;> simp [evaluate, read, inspect, found, zero, entered, called] at run
                        all_goals simpa [entered, called] using run
                    obtain ⟨jumped, jumpRun, finalSize⟩ := bodyIH body entered next _ smaller bodyRun
                    let original := { state with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }
                    exact ⟨original, jumpExc_transport entered state jumped rfl rfl jumpRun, finalSize⟩
                | some pair =>
                  obtain ⟨dest, names⟩ := pair
                  cases cut : cutEnv names state.locals with
                  | none => simp [evaluate, read, inspect, found, cut] at run
                  | some env =>
                    by_cases zero : state.clock = 0
                    · simp [evaluate, read, inspect, found, cut, zero] at run
                    · let entered := callEnv args size (pushEnv env false (decClock state))
                      have smaller : entered.clock < state.clock := by simp [entered, callEnv, pushEnv, decClock]; omega
                      cases called : fixClock entered (evaluate body entered) with
                      | mk outcome last =>
                        have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                        simp only [entered] at called
                        cases outcome with
                        | none => simp [evaluate, read, inspect, found, cut, zero, called] at run
                        | some outcome =>
                          cases outcome with
                          | val values =>
                            cases values with
                            | nil => simp [evaluate, read, inspect, found, cut, zero, called] at run
                            | cons first rest =>
                              cases rest with
                              | cons second rest => simp [evaluate, read, inspect, found, cut, zero, called] at run
                              | nil => cases popped : popEnv last <;> simp [evaluate, read, inspect, found, cut, zero, called, popped] at run
                          | err error =>
                            cases error with
                            | abort reason => simp [evaluate, read, inspect, found, cut, zero, called] at run
                            | raise value =>
                              simp [evaluate, read, inspect, found, cut, zero, called] at run
                              obtain ⟨rfl, rfl⟩ := run
                              obtain ⟨jumped, jumpRun, finalSize⟩ := bodyIH body entered last _ smaller bodyRun
                              obtain ⟨original, originalRun, jumpSize⟩ :=
                                jumpExc_callEnv_push_noHandler_inv_size state jumped env args size jumpRun
                              exact ⟨original, originalRun, finalSize.trans jumpSize⟩

/-- The call case of the frame-size invariant, assuming it for callee and
handler bodies at smaller clocks. -/
theorem evaluate_call_frameSizeResult {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (bodyIH : ∀ (body : DataLang.Prog) (entered finished : State C F) (outcome : Option (Result (List Value) Value)),
      entered.clock < state.clock → evaluate body entered = (outcome, finished) → frameSizeResult entered outcome finished)
    (run : evaluate (.call ret dest names handler) state = (result, next)) : frameSizeResult state result next := by
  cases result with
  | none =>
    cases handler with
    | none => exact evaluate_call_noHandler_normal_localsSize ret dest names state next run
    | some pair =>
      obtain ⟨name, handlerBody⟩ := pair
      apply evaluate_call_handler_normal_localsSize ret dest names name handlerBody state next
      · intro body entered finished value smaller called
        exact bodyIH body entered finished _ smaller called
      · intro body entered finished smaller called
        exact bodyIH body entered finished none smaller called
      · exact run
  | some outcome =>
    cases outcome with
    | val values => trivial
    | err error =>
      cases error with
      | abort reason => trivial
      | raise raised =>
        cases read : getVars names state.locals with
        | none => simp [evaluate, read] at run
        | some values =>
          cases found : findCode dest values state.code state.stackFrameSizes with
          | none => simp [evaluate, read, found] at run
          | some triple =>
            obtain ⟨args, body, size⟩ := triple
            cases ret with
            | none =>
              cases handler with
              | some pair => simp [evaluate, read, found] at run
              | none =>
                by_cases zero : state.clock = 0
                · simp [evaluate, read, found, zero] at run
                · let entered := callEnv args size (decClock state)
                  have smaller : entered.clock < state.clock := by simp [entered, callEnv, decClock]; omega
                  have bodyRun : evaluate body entered = (some (.err (.raise raised)), next) := by
                    cases called : evaluate body entered with
                    | mk outcome last =>
                      cases outcome <;> simp [evaluate, read, found, zero, entered, called] at run
                      all_goals simpa [entered, called] using run
                  obtain ⟨jumped, jumpRun, finalSize⟩ := bodyIH body entered next _ smaller bodyRun
                  let original := { state with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }
                  exact ⟨original, jumpExc_transport entered state jumped rfl rfl jumpRun, finalSize⟩
            | some pair =>
              obtain ⟨returns, live⟩ := pair
              by_cases nodup : returns.Nodup
              · cases cut : cutEnv live state.locals with
                | none => simp [evaluate, read, found, nodup, cut] at run
                | some env =>
                  by_cases zero : state.clock = 0
                  · simp [evaluate, read, found, nodup, cut, zero] at run
                  · let entered := callEnv args size (pushEnv env handler.isSome (decClock state))
                    have smaller : entered.clock < state.clock := by cases handler <;> simp [entered, callEnv, pushEnv, decClock] <;> omega
                    cases called : fixClock entered (evaluate body entered) with
                    | mk outcome last =>
                      have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                      have lastClock : last.clock < state.clock := by
                        have bound := evaluate_clock_le body entered
                        rw [bodyRun] at bound
                        exact Nat.lt_of_le_of_lt bound smaller
                      simp only [entered] at called
                      cases outcome with
                      | none => simp [evaluate, read, found, nodup, cut, zero, called] at run
                      | some outcome =>
                        cases outcome with
                        | val values =>
                          by_cases length : values.length = returns.length
                          · cases popped : popEnv last <;> simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                          · simp [evaluate, read, found, nodup, cut, zero, called, length] at run
                        | err error =>
                          cases error with
                          | abort reason => simp [evaluate, read, found, nodup, cut, zero, called] at run
                          | raise value =>
                            cases handler with
                            | none =>
                              simp only [Option.isSome] at called
                              simp [evaluate, read, found, nodup, cut, zero, called] at run
                              obtain ⟨rfl, rfl⟩ := run
                              obtain ⟨jumped, jumpRun, finalSize⟩ := bodyIH body entered last _ smaller bodyRun
                              obtain ⟨original, originalRun, jumpSize⟩ :=
                                jumpExc_callEnv_push_noHandler_inv_size state jumped env args size jumpRun
                              exact ⟨original, originalRun, finalSize.trans jumpSize⟩
                            | some pair =>
                              obtain ⟨name, handlerBody⟩ := pair
                              simp only [Option.isSome] at called
                              have control := evaluate_stackResult body entered last (some (.err (.raise value))) bodyRun
                              obtain ⟨jumped, jumpRun, afterStack, afterHandler, _⟩ := control
                              have expected := jumpExc_callEnv_push_handler state args size env
                              have jumpEq : jumped = { entered with stack := state.stack, handler := state.handler, locals := env, localsSize := state.localsSize } := by
                                apply Option.some.inj
                                rw [← jumpRun]
                                simpa [entered] using expected
                              have handlerRun : evaluate handlerBody (setVar name value last) = (some (.err (.raise raised)), next) := by
                                simpa [evaluate, read, found, nodup, cut, zero, called] using run
                              obtain ⟨handlerJump, handlerJumpRun, finalSize⟩ :=
                                bodyIH handlerBody (setVar name value last) next _ (by simpa [setVar] using lastClock) handlerRun
                              let original := { state with stack := handlerJump.stack, handler := handlerJump.handler, locals := handlerJump.locals, localsSize := handlerJump.localsSize }
                              have stack : (setVar name value last).stack = state.stack := by simpa [setVar, jumpEq] using afterStack
                              have handlerEq : (setVar name value last).handler = state.handler := by simpa [setVar, jumpEq] using afterHandler
                              exact ⟨original, jumpExc_transport (setVar name value last) state handlerJump stack.symm handlerEq.symm handlerJumpRun, finalSize⟩
              · simp [evaluate, read, found, nodup] at run

/-- Continuing evaluation preserves its entry frame size, while a raised
exception restores the size from the selected exception frame. This is
Flapjack auxiliary infrastructure rather than a tagged HOL theorem. -/
theorem evaluate_frameSizeResult {C F : Type} (program : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate program state = (result, next)) : frameSizeResult state result next := by
  have allRanks : ∀ clock weight : Nat, ∀ (program : DataLang.Prog) (state next : State C F)
      (result : Option (Result (List Value) Value)), state.clock = clock → sizeOf program = weight →
      evaluate program state = (result, next) → frameSizeResult state result next := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (program : DataLang.Prog) (state next : State C F)
            (result : Option (Result (List Value) Value)), state.clock ≤ clock → sizeOf program < weight →
            evaluate program state = (result, next) → frameSizeResult state result next := by
          intro program state next result clockLe weightLt run
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (sizeOf program) program state next result rfl rfl run
          · exact weightIH (sizeOf program) weightLt program state next result clockEq rfl run
        have smaller : ∀ (program : DataLang.Prog) (state next : State C F)
            (result : Option (Result (List Value) Value)), state.clock < clock →
            evaluate program state = (result, next) → frameSizeResult state result next := by
          intro program state next result clockLt run
          exact clockIH state.clock clockLt (sizeOf program) program state next result rfl rfl run
        intro program state next result stateClock measure run
        cases program with
        | skip => exact evaluate_skip_frameSizeResult state next result run
        | move dest src => exact evaluate_move_frameSizeResult dest src state next result run
        | assign dest op names live => exact evaluate_assign_frameSizeResult dest op names live state next result run
        | tick => exact evaluate_tick_frameSizeResult state next result run
        | makeSpace amount names => exact evaluate_makeSpace_frameSizeResult amount names state next result run
        | raise name => exact evaluate_raise_frameSizeResult name state next result run
        | «return» names => exact evaluate_return_frameSizeResult names state next result run
        | seq first second =>
          apply evaluate_seq_frameSizeResult first second state next result
          · intro after outcome firstRun
            apply exprIH first state after outcome (by omega)
            · simp only [DataLang.Prog.seq.sizeOf_spec] at measure; omega
            · exact firstRun
          · intro before after outcome bound secondRun
            apply exprIH second before after outcome (by omega)
            · simp only [DataLang.Prog.seq.sizeOf_spec] at measure; omega
            · exact secondRun
          · exact run
        | ifThenElse name yes no =>
          apply evaluate_if_frameSizeResult name yes no state next result
          · intro after outcome branchRun
            apply exprIH yes state after outcome (by omega)
            · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure; omega
            · exact branchRun
          · intro after outcome branchRun
            apply exprIH no state after outcome (by omega)
            · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure; omega
            · exact branchRun
          · exact run
        | force ret label src =>
          apply evaluate_force_frameSizeResult ret label src state next result
          · intro body entered finished outcome bound bodyRun
            exact smaller body entered finished outcome (by omega) bodyRun
          · exact run
        | call ret dest names handler =>
          apply evaluate_call_frameSizeResult ret dest names handler state next result
          · intro body entered finished outcome bound bodyRun
            exact smaller body entered finished outcome (by omega) bodyRun
          · exact run
  exact allRanks state.clock (sizeOf program) program state next result rfl rfl run

end Flapjack.Compiler.Backend.DataSem
