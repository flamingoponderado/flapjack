module

public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutSwap
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-! Resource-field variation for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

private def ResourceSwapAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (result : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (flag : Bool) (mx : Option Nat) (safe : Bool) (peak : Nat),
    evaluate program state = (result, next) →
    if flag then
      ∃ mx' safe' peak',
        evaluate program { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
          (result, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' })
    else
      ∃ safe' peak',
        evaluate program { state with stackMax := state.stackMax, safeForSpace := safe, peakHeapLength := peak } =
          (result, { next with stackMax := next.stackMax, safeForSpace := safe', peakHeapLength := peak' })

private theorem popEnv_resourceUpdate {C F : Type} (state : State C F)
    (mx : Option Nat) (safe : Bool) (peak : Nat) :
    popEnv { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
      (popEnv state).map (fun next =>
        { next with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }) := by
  cases frames : state.stack with
  | nil => simp [popEnv, frames]
  | cons frame rest => cases frame <;> simp [popEnv, frames]

private theorem popEnv_stackMax {C F : Type} (state next : State C F)
    (run : popEnv state = some next) : next.stackMax = state.stackMax := by
  cases frames : state.stack with
  | nil => simp [popEnv, frames] at run
  | cons frame rest =>
    cases frame <;> simp [popEnv, frames] at run <;> subst next <;> rfl

private theorem resourceSwap_skip {C F : Type} (state : State C F) :
    ResourceSwapAt .skip state := by
  intro result next flag mx safe peak run
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  cases flag <;> simp [evaluate]

private theorem resourceSwap_move {C F : Type} (dest src : Nat) (state : State C F) :
    ResourceSwapAt (.move dest src) state := by
  intro result next flag mx safe peak run
  cases read : getVar src state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some value =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read, setVar]

private theorem resourceSwap_tick {C F : Type} (state : State C F) :
    ResourceSwapAt .tick state := by
  intro result next flag mx safe peak run
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, zero, flushState]
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, zero, decClock]

private theorem resourceSwap_return {C F : Type} (names : List Nat) (state : State C F) :
    ResourceSwapAt (.return names) state := by
  intro result next flag mx safe peak run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some values =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read, flushState]

private theorem resourceSwap_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : ResourceSwapAt (.makeSpace amount names) state := by
  intro result next flag mx safe peak run
  cases cut : cutEnv names state.locals with
  | none =>
    simp [evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, cut]
  | some env =>
    simp [evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, cut, addSpace]

private theorem jumpExc_resourceUpdate {C F : Type} (state : State C F)
    (mx : Option Nat) (safe : Bool) (peak : Nat) :
    jumpExc { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
      (jumpExc state).map (fun next =>
        { next with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }) := by
  simp only [jumpExc]
  split
  next =>
    cases frames : state.stack.drop (state.stack.length - (state.handler + 1)) with
    | nil => rfl
    | cons frame rest => cases frame <;> rfl
  next => rfl

private theorem resourceSwap_raise {C F : Type} (name : Nat) (state : State C F) :
    ResourceSwapAt (.raise name) state := by
  intro result next flag mx safe peak run
  cases read : getVar name state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some value =>
    cases jumped : jumpExc state with
    | none =>
      simp [evaluate, read, jumped] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, jumpExc_resourceUpdate, jumped]
    | some last =>
      have sameMax : last.stackMax = state.stackMax := by
        unfold jumpExc at jumped
        split at jumped
        next =>
          cases frames : state.stack.drop (state.stack.length - (state.handler + 1)) with
          | nil => simp [frames] at jumped
          | cons frame rest =>
            cases frame <;> simp [frames] at jumped
            subst last
            rfl
        next => simp at jumped
      simp [evaluate, read, jumped] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, jumpExc_resourceUpdate, jumped, sameMax]

private theorem resourceSwap_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    ResourceSwapAt (.assign dest op names live) state := by
  intro result next flag mx safe peak run
  by_cases invalid : DataLang.opRequiresNames op == live.isNone
  · simp [evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, invalid]
  · cases read : DataSem.getVars names state.locals with
    | none =>
      simp [evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, invalid, read]
    | some values =>
      cases cut : cutStateOpt live state with
      | none =>
        simp [evaluate, invalid, read, cut] at run
        obtain ⟨rfl, rfl⟩ := run
        cases flag <;> simp [evaluate, invalid, read, cutStateOpt_withSwap, cut]
      | some mid =>
        have midMax := cutStateOpt_stackMax live state mid cut
        cases app : doApp op values mid with
        | err error =>
          simp [evaluate, invalid, read, cut, app] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag with
          | false =>
            have swapped := doApp_err_safePeakSwap op values mid error safe peak app
            simp [evaluate, invalid, read, cutStateOpt_withSwap, cut, ← midMax,
              swapped, flushState, installSfs]
          | true =>
            have swapped := doApp_err_stackSafePeakSwap op values mid error mx safe peak app
            simp [evaluate, invalid, read, cutStateOpt_withSwap, cut,
              swapped, flushState, installSfs]
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [evaluate, invalid, read, cut, app] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag with
          | false =>
            obtain ⟨safe', peak', swapped⟩ := doApp_safePeakSwap op values mid value last safe peak app
            simp [evaluate, invalid, read, cutStateOpt_withSwap, cut, ← midMax,
              swapped, setVar, installSfs]
          | true =>
            obtain ⟨safe', peak', mx', swapped⟩ := doApp_stackSafePeakSwap op values mid value last mx safe peak app
            simp [evaluate, invalid, read, cutStateOpt_withSwap, cut,
              swapped, setVar, installSfs]

private theorem resourceSwap_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : ResourceSwapAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → ResourceSwapAt second mid) :
    ResourceSwapAt (.seq first second) state := by
  intro result next flag mx safe peak run
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    have clockBound : mid.clock ≤ state.clock := by
      simpa only [firstRun] using evaluate_clock_le first state
    cases outcome with
    | none =>
      simp only [evaluate] at run
      rw [fixClock_evaluate, firstRun] at run
      cases flag with
      | false =>
        obtain ⟨safe1, peak1, firstSwap⟩ := firstIH none mid false mx safe peak firstRun
        obtain ⟨safe2, peak2, secondSwap⟩ := secondIH mid clockBound result next false mx safe1 peak1 run
        refine ⟨safe2, peak2, ?_⟩
        simp only [evaluate]
        rw [fixClock_evaluate, firstSwap]

        exact secondSwap
      | true =>
        obtain ⟨mx1, safe1, peak1, firstSwap⟩ := firstIH none mid true mx safe peak firstRun
        obtain ⟨mx2, safe2, peak2, secondSwap⟩ := secondIH mid clockBound result next true mx1 safe1 peak1 run
        refine ⟨mx2, safe2, peak2, ?_⟩
        simp only [evaluate]
        rw [fixClock_evaluate, firstSwap]
        exact secondSwap
    | some stopped =>
      simp only [evaluate] at run
      rw [fixClock_evaluate, firstRun] at run
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag with
      | false =>
        obtain ⟨safe1, peak1, firstSwap⟩ := firstIH (some stopped) mid false mx safe peak firstRun
        refine ⟨safe1, peak1, ?_⟩
        simp only [evaluate]
        rw [fixClock_evaluate, firstSwap]
      | true =>
        obtain ⟨mx1, safe1, peak1, firstSwap⟩ := firstIH (some stopped) mid true mx safe peak firstRun
        refine ⟨mx1, safe1, peak1, ?_⟩
        simp only [evaluate]
        rw [fixClock_evaluate, firstSwap]

private theorem resourceSwap_tailCall {C F : Type} (dest : Option Nat) (names : List Nat)
    (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → ResourceSwapAt body called) :
    ResourceSwapAt (.call none dest names handler) state := by
  intro result next flag mx safe peak run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp [evaluate, read, found] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, found]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      cases handler with
      | some handler =>
        simp [evaluate, read, found] at run
        obtain ⟨rfl, rfl⟩ := run
        cases flag <;> simp [evaluate, read, found]
      | none =>
        by_cases zero : state.clock = 0
        · simp [evaluate, read, found, zero] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, found, zero, flushState]
        · let called := DataSem.callEnv args size (decClock state)
          have clockLt : called.clock < state.clock := by
            simp [called, DataSem.callEnv, decClock]
            omega
          cases bodyRun : evaluate body called with
          | mk outcome last =>
            cases flag with
            | false =>
              let changed := DataSem.callEnv args size (decClock { state with safeForSpace := safe, peakHeapLength := peak })
              obtain ⟨safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last false mx changed.safeForSpace peak bodyRun
              have changedRun : evaluate body changed =
                  (outcome, { last with safeForSpace := safe1, peakHeapLength := peak1 }) := by
                simpa [changed, called, DataSem.callEnv, decClock] using swapped
              simp only [called] at bodyRun
              simp only [changed] at changedRun
              cases outcome <;> simp [evaluate, read, found, zero, bodyRun] at run
              all_goals
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨safe1, peak1, ?_⟩
                simp [evaluate, read, found, zero, changedRun]
            | true =>
              let changed := DataSem.callEnv args size (decClock { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak })
              obtain ⟨mx1, safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last true changed.stackMax changed.safeForSpace peak bodyRun
              have changedRun : evaluate body changed =
                  (outcome, { last with stackMax := mx1, safeForSpace := safe1, peakHeapLength := peak1 }) := by
                simpa [changed, called, DataSem.callEnv, decClock] using swapped
              simp only [called] at bodyRun
              simp only [changed] at changedRun
              cases outcome <;> simp [evaluate, read, found, zero, bodyRun] at run
              all_goals
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨mx1, safe1, peak1, ?_⟩
                simp [evaluate, read, found, zero, changedRun]

private theorem resourceSwap_tailForce {C F : Type} (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → ResourceSwapAt body called) :
    ResourceSwapAt (.force none label src) state := by
  intro result next flag mx safe peak run
  cases read : getVar src state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef | notThunk =>
      simp [evaluate, read, th] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [evaluate, read, th] at run
        obtain ⟨rfl, rfl⟩ := run
        cases flag <;> simp [evaluate, read, th, flushState]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp [evaluate, read, th, found] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, th, found]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          by_cases zero : state.clock = 0
          · simp [evaluate, read, th, found, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            cases flag <;> simp [evaluate, read, th, found, zero]
          · let called := DataSem.callEnv args size (decClock state)
            have clockLt : called.clock < state.clock := by
              simp [called, DataSem.callEnv, decClock]
              omega
            cases bodyRun : evaluate body called with
            | mk outcome last =>
              cases flag with
              | false =>
                let changed := DataSem.callEnv args size (decClock { state with safeForSpace := safe, peakHeapLength := peak })
                obtain ⟨safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last false mx changed.safeForSpace peak bodyRun
                have changedRun : evaluate body changed =
                    (outcome, { last with safeForSpace := safe1, peakHeapLength := peak1 }) := by
                  simpa [changed, called, DataSem.callEnv, decClock] using swapped
                simp only [called] at bodyRun
                simp only [changed] at changedRun
                cases outcome <;> simp [evaluate, read, th, found, zero, bodyRun] at run
                all_goals
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨safe1, peak1, ?_⟩
                  simp [evaluate, read, th, found, zero, changedRun]
              | true =>
                let changed := DataSem.callEnv args size (decClock { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak })
                obtain ⟨mx1, safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last true changed.stackMax changed.safeForSpace peak bodyRun
                have changedRun : evaluate body changed =
                    (outcome, { last with stackMax := mx1, safeForSpace := safe1, peakHeapLength := peak1 }) := by
                  simpa [changed, called, DataSem.callEnv, decClock] using swapped
                simp only [called] at bodyRun
                simp only [changed] at changedRun
                cases outcome <;> simp [evaluate, read, th, found, zero, bodyRun] at run
                all_goals
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨mx1, safe1, peak1, ?_⟩
                  simp [evaluate, read, th, found, zero, changedRun]

private theorem resourceSwap_returningForce {C F : Type} (dest : Nat) (live : NumSet)
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → ResourceSwapAt body called) :
    ResourceSwapAt (.force (some (dest, live)) label src) state := by
  intro result next flag mx safe peak run
  cases read : getVar src state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef | notThunk =>
      simp [evaluate, read, th] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv live state.locals with
        | none =>
          simp [evaluate, read, th, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, th, cut]
        | some env =>
          simp [evaluate, read, th, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, th, cut, setVar]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp [evaluate, read, th, found] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, th, found]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          cases cut : cutEnv live state.locals with
          | none =>
            simp [evaluate, read, th, found, cut] at run
            obtain ⟨rfl, rfl⟩ := run
            cases flag <;> simp [evaluate, read, th, found, cut]
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, th, found, cut, zero] at run
              obtain ⟨rfl, rfl⟩ := run
              cases flag <;> simp [evaluate, read, th, found, cut, zero,
                DataSem.callEnv, pushEnv, decClock]
            · let called := DataSem.callEnv args size (pushEnv env false (decClock state))
              have clockLt : called.clock < state.clock := by
                simp [called, DataSem.callEnv, pushEnv, decClock]
                omega
              cases bodyRun : evaluate body called with
              | mk outcome last =>
                cases flag with
                | false =>
                  let changed := DataSem.callEnv args size (pushEnv env false
                    (decClock { state with safeForSpace := safe, peakHeapLength := peak }))
                  obtain ⟨safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last false mx changed.safeForSpace peak bodyRun
                  have changedRun : evaluate body changed =
                      (outcome, { last with safeForSpace := safe1, peakHeapLength := peak1 }) := by
                    simpa [changed, called, DataSem.callEnv, pushEnv, decClock] using swapped
                  simp only [evaluate, read, th, found, cut, zero, ite_false] at run ⊢
                  simp only [fixClock_evaluate] at run ⊢
                  simp only [called] at bodyRun
                  rw [bodyRun] at run
                  refine ⟨safe1, peak1, ?_⟩
                  simp only [changed] at changedRun
                  rw [changedRun]
                  cases outcome with
                  | none => simp_all
                  | some outcome =>
                    cases outcome with
                    | err error => simp_all
                    | val values =>
                      cases values with
                      | nil => simp_all
                      | cons value rest =>
                        cases rest with
                        | cons value' rest => simp_all
                        | nil =>
                          cases popped : popEnv last with
                          | none => simp_all [popEnv_resourceUpdate]
                          | some restored =>
                            have sameMax := popEnv_stackMax last restored popped
                            simp_all [popEnv_resourceUpdate, setVar]
                            rcases run with ⟨rfl, rfl⟩
                            simp
                | true =>
                  let changed := DataSem.callEnv args size (pushEnv env false
                    (decClock { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }))
                  obtain ⟨mx1, safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last true changed.stackMax changed.safeForSpace peak bodyRun
                  have changedRun : evaluate body changed =
                      (outcome, { last with stackMax := mx1, safeForSpace := safe1, peakHeapLength := peak1 }) := by
                    simpa [changed, called, DataSem.callEnv, pushEnv, decClock] using swapped
                  simp only [evaluate, read, th, found, cut, zero, ite_false] at run ⊢
                  simp only [fixClock_evaluate] at run ⊢
                  simp only [called] at bodyRun
                  rw [bodyRun] at run
                  refine ⟨mx1, safe1, peak1, ?_⟩
                  simp only [changed] at changedRun
                  rw [changedRun]
                  cases outcome with
                  | none => simp_all
                  | some outcome =>
                    cases outcome with
                    | err error => simp_all
                    | val values =>
                      cases values with
                      | nil => simp_all
                      | cons value rest =>
                        cases rest with
                        | cons value' rest => simp_all
                        | nil =>
                          cases popped : popEnv last with
                          | none => simp_all [popEnv_resourceUpdate]
                          | some restored =>
                            simp_all [popEnv_resourceUpdate, setVar]
                            rcases run with ⟨rfl, rfl⟩
                            simp

private theorem resourceSwap_returningCall {C F : Type} (returns : List Nat) (live : NumSet)
    (dest : Option Nat) (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → ResourceSwapAt body called)
    (handlerIH : ∀ (name : Nat) (body : DataLang.Prog) (entered : State C F),
      handler = some (name, body) → entered.clock ≤ state.clock → ResourceSwapAt body entered) :
    ResourceSwapAt (.call (some (returns, live)) dest names handler) state := by
  intro result next flag mx safe peak run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp [evaluate, read, found] at run
      obtain ⟨rfl, rfl⟩ := run
      cases flag <;> simp [evaluate, read, found]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp [evaluate, read, found, distinct, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flag <;> simp [evaluate, read, found, distinct, cut]
        | some env =>
          by_cases zero : state.clock = 0
          · simp [evaluate, read, found, distinct, cut, zero] at run
            obtain ⟨rfl, rfl⟩ := run
            cases flag <;> simp [evaluate, read, found, distinct, cut, zero,
              DataSem.callEnv, pushEnv, decClock]
          · let called := DataSem.callEnv args size (pushEnv env handler.isSome (decClock state))
            have clockLt : called.clock < state.clock := by
              simp [called, DataSem.callEnv, pushEnv, decClock]
              omega
            cases bodyRun : evaluate body called with
            | mk outcome last =>
              have lastClock : last.clock ≤ state.clock := by
                have bound := evaluate_clock_le body called
                rw [bodyRun] at bound
                change last.clock ≤ called.clock at bound
                omega
              cases flag with
              | false =>
                let changed := DataSem.callEnv args size (pushEnv env handler.isSome
                  (decClock { state with safeForSpace := safe, peakHeapLength := peak }))
                obtain ⟨safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last false mx changed.safeForSpace peak bodyRun
                have changedRun : evaluate body changed =
                    (outcome, { last with safeForSpace := safe1, peakHeapLength := peak1 }) := by
                  simpa [changed, called, DataSem.callEnv, pushEnv, decClock] using swapped
                simp only [evaluate, read, found, distinct, cut, zero, ite_false] at run ⊢
                simp only [fixClock_evaluate] at run ⊢
                simp only [called] at bodyRun
                rw [bodyRun] at run
                simp only [changed] at changedRun
                rw [changedRun]
                cases outcome with
                | none =>
                  refine ⟨safe1, peak1, ?_⟩
                  simp_all
                | some outcome =>
                  cases outcome with
                  | val returned =>
                    by_cases lengthEq : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none =>
                        refine ⟨safe1, peak1, ?_⟩
                        simp_all [popEnv_resourceUpdate]
                      | some restored =>
                        have sameMax := popEnv_stackMax last restored popped
                        refine ⟨safe1, peak1, ?_⟩
                        simp_all [popEnv_resourceUpdate, setVars]
                        rcases run with ⟨rfl, rfl⟩
                        simp
                    · refine ⟨safe1, peak1, ?_⟩
                      simp_all
                  | err error =>
                    cases error with
                    | abort reason =>
                      refine ⟨safe1, peak1, ?_⟩
                      simp_all
                    | raise value =>
                      cases handler with
                      | none =>
                        refine ⟨safe1, peak1, ?_⟩
                        simp_all
                      | some entry =>
                        obtain ⟨name, handlerBody⟩ := entry
                        have handlerClock : (setVar name value last).clock ≤ state.clock := by
                          simpa [setVar] using lastClock
                        have handlerRun : evaluate handlerBody (setVar name value last) = (result, next) := by
                          simpa using run
                        obtain ⟨safe2, peak2, handlerSwap⟩ :=
                          handlerIH name handlerBody (setVar name value last) rfl handlerClock result next false mx safe1 peak1 handlerRun
                        refine ⟨safe2, peak2, ?_⟩
                        simpa [setVar] using handlerSwap
              | true =>
                let changed := DataSem.callEnv args size (pushEnv env handler.isSome
                  (decClock { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }))
                obtain ⟨mx1, safe1, peak1, swapped⟩ := bodyIH body called clockLt outcome last true changed.stackMax changed.safeForSpace peak bodyRun
                have changedRun : evaluate body changed =
                    (outcome, { last with stackMax := mx1, safeForSpace := safe1, peakHeapLength := peak1 }) := by
                  simpa [changed, called, DataSem.callEnv, pushEnv, decClock] using swapped
                simp only [evaluate, read, found, distinct, cut, zero, ite_false] at run ⊢
                simp only [fixClock_evaluate] at run ⊢
                simp only [called] at bodyRun
                rw [bodyRun] at run
                simp only [changed] at changedRun
                rw [changedRun]
                cases outcome with
                | none =>
                  refine ⟨mx1, safe1, peak1, ?_⟩
                  simp_all
                | some outcome =>
                  cases outcome with
                  | val returned =>
                    by_cases lengthEq : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none =>
                        refine ⟨mx1, safe1, peak1, ?_⟩
                        simp_all [popEnv_resourceUpdate]
                      | some restored =>
                        refine ⟨mx1, safe1, peak1, ?_⟩
                        simp_all [popEnv_resourceUpdate, setVars]
                        rcases run with ⟨rfl, rfl⟩
                        simp
                    · refine ⟨mx1, safe1, peak1, ?_⟩
                      simp_all
                  | err error =>
                    cases error with
                    | abort reason =>
                      refine ⟨mx1, safe1, peak1, ?_⟩
                      simp_all
                    | raise value =>
                      cases handler with
                      | none =>
                        refine ⟨mx1, safe1, peak1, ?_⟩
                        simp_all
                      | some entry =>
                        obtain ⟨name, handlerBody⟩ := entry
                        have handlerClock : (setVar name value last).clock ≤ state.clock := by
                          simpa [setVar] using lastClock
                        have handlerRun : evaluate handlerBody (setVar name value last) = (result, next) := by
                          simpa using run
                        obtain ⟨mx2, safe2, peak2, handlerSwap⟩ :=
                          handlerIH name handlerBody (setVar name value last) rfl handlerClock result next true mx1 safe1 peak1 handlerRun
                        refine ⟨mx2, safe2, peak2, ?_⟩
                        simpa [setVar] using handlerSwap
      · simp [evaluate, read, found, distinct] at run
        obtain ⟨rfl, rfl⟩ := run
        cases flag <;> simp [evaluate, read, found, distinct]

private theorem resourceSwap_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : ResourceSwapAt yes state) (noIH : ResourceSwapAt no state) :
    ResourceSwapAt (.ifThenElse name yes no) state := by
  intro result next flag mx safe peak run
  cases read : getVar name state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flag <;> simp [evaluate, read]
  | some value =>
    by_cases yesValue : isBool true value
    · simp only [evaluate, read, yesValue, ite_true] at run
      simpa only [evaluate, read, yesValue, ite_true] using yesIH result next flag mx safe peak run
    · by_cases noValue : isBool false value
      · simp only [evaluate, read, yesValue, noValue, ite_true] at run
        simpa only [evaluate, read, yesValue, noValue, Bool.false_eq_true, ite_true, ite_false] using
          noIH result next flag mx safe peak run
      · simp [evaluate, read, yesValue, noValue] at run
        obtain ⟨rfl, rfl⟩ := run
        cases flag <;> simp [evaluate, read, yesValue, noValue]

private theorem resourceSwap_all {C F : Type} (program : DataLang.Prog) (state : State C F) :
    ResourceSwapAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => ResourceSwapAt program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact resourceSwap_skip state
  | move dest src => exact resourceSwap_move dest src state
  | assign dest op names live => exact resourceSwap_assign dest op names live state
  | tick => exact resourceSwap_tick state
  | makeSpace amount names => exact resourceSwap_makeSpace amount names state
  | raise name => exact resourceSwap_raise name state
  | «return» names => exact resourceSwap_return names state
  | seq first second =>
    apply resourceSwap_seq first second state
    · apply exprIH first state (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
    · intro mid bound
      apply exprIH second mid bound
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
  | ifThenElse name yes no =>
    apply resourceSwap_if name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
  | force ret label src =>
    cases ret with
    | none => exact resourceSwap_tailForce label src state smaller
    | some ret =>
      obtain ⟨dest, live⟩ := ret
      exact resourceSwap_returningForce dest live label src state smaller
  | call ret dest names handler =>
    cases ret with
    | none => exact resourceSwap_tailCall dest names handler state smaller
    | some ret =>
      obtain ⟨returns, live⟩ := ret
      apply resourceSwap_returningCall returns live dest names handler state smaller
      intro name body entered isHandler bound
      subst handler
      apply exprIH body entered bound
      simp only [DataLang.Prog.call.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]
      omega

/-- Evaluation is preserved when the recorded resource observations vary.
The false branch omits HOL's unused existential over an independent type:
it is vacuous because HOL types are inhabited. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_fl_smx_safe_peak_swap_aux"]
theorem evaluate_flagStackSafePeakSwap {C F : Type} (program : DataLang.Prog) (state : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (flag : Bool) (mx : Option Nat) (safe : Bool) (peak : Nat)
    (run : evaluate program state = (result, next)) :
    if flag then
      let s0 := { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }
      ∃ mx' safe' peak', evaluate program s0 =
        (result, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' })
    else
      let s0 := { state with stackMax := state.stackMax, safeForSpace := safe, peakHeapLength := peak }
      ∃ safe' peak', evaluate program s0 =
        (result, { next with stackMax := next.stackMax, safeForSpace := safe', peakHeapLength := peak' }) :=
  resourceSwap_all program state result next flag mx safe peak run

/-- Stack, safety, and peak updates preserve the evaluation result. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_smx_safe_peak_swap_aux"]
theorem evaluate_stackSafePeakSwapAux {C F : Type} (mx : Option Nat) (safe : Bool)
    (next state : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (peak : Nat) (program : DataLang.Prog) (run : evaluate program state = (result, next)) :
    let s0 := { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak }
    ∃ mx' safe' peak', evaluate program s0 =
      (result, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) := by
  simpa only [ite_true] using evaluate_flagStackSafePeakSwap program state result next true mx safe peak run

/-- Evaluation commutes with arbitrary stack, safety, and peak updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_smx_safe_peak_swap"]
theorem evaluate_stackSafePeakSwap {C F : Type} (mx : Option Nat) (safe : Bool)
    (next state : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (peak : Nat) (program : DataLang.Prog) (run : evaluate program state = (result, next)) :
    ∃ mx' safe' peak', evaluate program { state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak } =
      (result, { next with stackMax := mx', safeForSpace := safe', peakHeapLength := peak' }) :=
  evaluate_stackSafePeakSwapAux mx safe next state result peak program run

/-- Safety and peak updates preserve evaluation with the stack maximum fixed. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_safe_peak_swap_aux"]
theorem evaluate_safePeakSwapAux {C F : Type} (safe : Bool) (next state : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (peak : Nat)
    (program : DataLang.Prog) (run : evaluate program state = (result, next)) :
    let s0 := { state with stackMax := state.stackMax, safeForSpace := safe, peakHeapLength := peak }
    ∃ safe' peak', evaluate program s0 =
      (result, { next with stackMax := next.stackMax, safeForSpace := safe', peakHeapLength := peak' }) := by
  simpa only [Bool.false_eq_true, ite_false] using
    evaluate_flagStackSafePeakSwap program state result next false state.stackMax safe peak run

/-- Safety and peak updates preserve the evaluation result and stack maximum. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_safe_peak_swap"]
theorem evaluate_safePeakSwap {C F : Type} (safe : Bool) (next state : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (peak : Nat)
    (program : DataLang.Prog) (run : evaluate program state = (result, next)) :
    ∃ safe' peak', evaluate program { state with safeForSpace := safe, peakHeapLength := peak } =
      (result, { next with safeForSpace := safe', peakHeapLength := peak' }) :=
  evaluate_safePeakSwapAux safe next state result peak program run

end Flapjack.Compiler.Backend.DataProps
