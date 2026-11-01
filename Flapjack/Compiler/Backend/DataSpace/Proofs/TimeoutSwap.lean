import Flapjack.Compiler.Backend.DataSpace.Proofs.ResourceVariation

/-! Timeout behavior of primitive applications. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Installation cannot produce a timeout. -/
theorem doInstall_ne_timeout {C F : Type} (args : List DataSem.Value) (state : State C F) :
    doInstall (R := DataSem.Value) args state ≠ .err (.abort .timeoutError) := by
  simp only [doInstall]
  repeat' (split <;> try simp_all)

/-- The primitive dispatcher can return type errors or FFI errors, but cannot
produce a timeout. -/
theorem doAppAux_ne_timeout {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) : doAppAux op args state ≠ .err (.abort .timeoutError) := by
  simp only [doAppAux]
  repeat' (split <;> try simp_all)

/-- Resource accounting and installation do not introduce a timeout. -/
theorem doApp_ne_timeout {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) : doApp op args state ≠ .err (.abort .timeoutError) := by
  cases op with
  | install => exact doInstall_ne_timeout args _
  | intOp op => cases op <;> simp only [doApp] <;> (try split) <;> simp_all [doAppAux_ne_timeout]
  | label label => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | ffi name => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | wordOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | blockOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | globOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | memOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]
  | thunkOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_timeout]

/-- Assignment evaluation cannot be the source of a timeout. -/
theorem evaluate_assign_ne_timeout {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state next : State C F) :
    DataSem.evaluate (.assign dest op names live) state ≠ (some (.err (.abort .timeoutError)), next) := by
  intro run
  simp only [DataSem.evaluate] at run
  repeat' (split at run <;> try simp_all)
  all_goals simp_all [doApp_ne_timeout]

/-- A force that immediately times out has the same final frame size after
changing only the resource-accounting fields. -/
theorem evaluate_force_timeout_zero_size {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state next targetNext : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (zero : state.clock = 0)
    (run : DataSem.evaluate (.force ret label src) state = (some (.err (.abort .timeoutError)), next))
    (targetRun : DataSem.evaluate (.force ret label src)
      { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), targetNext)) : next.localsSize = targetNext.localsSize := by
  cases read : getVar src state.locals with
  | none => simp [DataSem.evaluate, read] at run
  | some thunk =>
    cases inspect : destThunk thunk state.refs with
    | badRef => simp [DataSem.evaluate, read, inspect] at run
    | notThunk => simp [DataSem.evaluate, read, inspect] at run
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases ret with
        | none => simp [DataSem.evaluate, read, inspect] at run
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          cases cut : cutEnv names state.locals <;> simp [DataSem.evaluate, read, inspect, cut] at run
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none => simp [DataSem.evaluate, read, inspect, found] at run
        | some triple =>
          obtain ⟨args, body, size⟩ := triple
          cases ret with
          | none =>
            simp [DataSem.evaluate, read, inspect, found, zero] at run targetRun
            subst next
            subst targetNext
            rfl
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals with
            | none => simp [DataSem.evaluate, read, inspect, found, cut] at run
            | some env =>
              simp [DataSem.evaluate, read, inspect, found, cut, zero] at run targetRun
              subst next
              subst targetNext
              rfl

/-- A call that immediately times out has the same final frame size after
changing only the resource-accounting fields. -/
theorem evaluate_call_timeout_zero_size {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (names : List Nat) (handler : Option (Nat × DataLang.Prog))
    (state next targetNext : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (zero : state.clock = 0)
    (run : DataSem.evaluate (.call ret dest names handler) state = (some (.err (.abort .timeoutError)), next))
    (targetRun : DataSem.evaluate (.call ret dest names handler)
      { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), targetNext)) : next.localsSize = targetNext.localsSize := by
  cases read : DataSem.getVars names state.locals with
  | none => simp [DataSem.evaluate, read] at run
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [DataSem.evaluate, read, found] at run
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none =>
        cases handler with
        | some pair => simp [DataSem.evaluate, read, found] at run
        | none =>
          simp [DataSem.evaluate, read, found, zero] at run targetRun
          subst next
          subst targetNext
          rfl
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [DataSem.evaluate, read, found, nodup, cut] at run
          | some env =>
            cases handler <;> simp [DataSem.evaluate, read, found, nodup, cut, zero] at run targetRun
            all_goals subst next
            all_goals subst targetNext
            all_goals rfl
        · simp [DataSem.evaluate, read, found, nodup] at run

/-- At a zero clock, a timeout has the same final frame size after varying
the resource-accounting fields. -/
theorem evaluate_timeout_zeroClock_size {C F : Type} (program : DataLang.Prog)
    (state next targetNext : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (zero : state.clock = 0)
    (run : DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next))
    (targetRun : DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
      (some (.err (.abort .timeoutError)), targetNext)) : next.localsSize = targetNext.localsSize := by
  have allSizes : ∀ weight : Nat, ∀ (program : DataLang.Prog) (state next targetNext : State C F)
      (safe : Bool) (peak : Nat) (stackMax : Option Nat), sizeOf program = weight → state.clock = 0 →
      DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next) →
      DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), targetNext) → next.localsSize = targetNext.localsSize := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program state next targetNext safe peak stackMax measure zero run targetRun
      have smaller : ∀ (child : DataLang.Prog) (state next targetNext : State C F)
          (safe : Bool) (peak : Nat) (stackMax : Option Nat), sizeOf child < weight → state.clock = 0 →
          DataSem.evaluate child state = (some (.err (.abort .timeoutError)), next) →
          DataSem.evaluate child { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
            (some (.err (.abort .timeoutError)), targetNext) → next.localsSize = targetNext.localsSize := by
        intro child state next targetNext safe peak stackMax less zero run targetRun
        exact ih (sizeOf child) less child state next targetNext safe peak stackMax rfl zero run targetRun
      cases program with
      | skip => simp [DataSem.evaluate] at run
      | move dest src => cases read : getVar src state.locals <;> simp [DataSem.evaluate, read] at run
      | assign dest op args names => exact False.elim (evaluate_assign_ne_timeout dest op args names state next run)
      | tick =>
        simp [DataSem.evaluate, zero, flushState] at run targetRun
        subst next
        subst targetNext
        rfl
      | makeSpace amount names => cases cut : cutEnv names state.locals <;> simp [DataSem.evaluate, cut] at run
      | raise name =>
        cases read : getVar name state.locals with
        | none => simp [DataSem.evaluate, read] at run
        | some value => cases jump : jumpExc state <;> simp [DataSem.evaluate, read, jump] at run
      | «return» names => cases read : DataSem.getVars names state.locals <;> simp [DataSem.evaluate, read] at run
      | seq first second =>
        rw [DataSem.evaluate, fixClock_evaluate] at run targetRun
        cases firstRun : DataSem.evaluate first state with
        | mk outcome mid =>
          rw [firstRun] at run
          cases outcome with
          | some result =>
            simp only [Prod.mk.injEq, Option.some.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            obtain ⟨matched, matchedRun, _, _⟩ := evaluate_resource_variation first state mid
              (some (.err (.abort .timeoutError))) safe peak stackMax firstRun (by simp)
            rw [matchedRun] at targetRun
            simp only [Prod.mk.injEq] at targetRun
            obtain ⟨_, rfl⟩ := targetRun
            apply smaller first state mid matched safe peak stackMax ?_ zero firstRun matchedRun
            simp only [DataLang.Prog.seq.sizeOf_spec] at measure
            omega
          | none =>
            obtain ⟨safe', peak', max', varied⟩ := evaluate_resource_variation_normal first state mid safe peak stackMax firstRun
            rw [varied] at targetRun
            have midZero : mid.clock = 0 := by
              have bound := evaluate_clock_le first state
              rw [firstRun] at bound
              change mid.clock ≤ state.clock at bound
              omega
            apply smaller second mid next targetNext safe' peak' max' ?_ midZero run targetRun
            simp only [DataLang.Prog.seq.sizeOf_spec] at measure
            omega
      | ifThenElse name yes no =>
        cases read : getVar name state.locals with
        | none => simp [DataSem.evaluate, read] at run
        | some value =>
          by_cases yesTest : isBool true value
          · have sourceBranch : DataSem.evaluate yes state = (some (.err (.abort .timeoutError)), next) := by
              simpa [DataSem.evaluate, read, yesTest] using run
            have targetBranch : DataSem.evaluate yes { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } = (some (.err (.abort .timeoutError)), targetNext) := by
              simpa [DataSem.evaluate, read, yesTest] using targetRun
            apply smaller yes state next targetNext safe peak stackMax ?_ zero sourceBranch targetBranch
            simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
            omega
          · by_cases noTest : isBool false value
            · have sourceBranch : DataSem.evaluate no state = (some (.err (.abort .timeoutError)), next) := by
                simpa [DataSem.evaluate, read, yesTest, noTest] using run
              have targetBranch : DataSem.evaluate no { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } = (some (.err (.abort .timeoutError)), targetNext) := by
                simpa [DataSem.evaluate, read, yesTest, noTest] using targetRun
              apply smaller no state next targetNext safe peak stackMax ?_ zero sourceBranch targetBranch
              simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
              omega
            · simp [DataSem.evaluate, read, yesTest, noTest] at run
      | force ret label src => exact evaluate_force_timeout_zero_size ret label src state next targetNext safe peak stackMax zero run targetRun
      | call ret dest names handler => exact evaluate_call_timeout_zero_size ret dest names handler state next targetNext safe peak stackMax zero run targetRun
  exact allSizes (sizeOf program) program state next targetNext safe peak stackMax rfl zero run targetRun

/-- The exact resource-field swap for a timeout at zero entry clock. -/
theorem evaluate_resource_variation_timeout_zero {C F : Type} (program : DataLang.Prog)
    (state next : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (zero : state.clock = 0)
    (run : DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), { next with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program state next (some (.err (.abort .timeoutError))) safe peak stackMax run (by simp)
  have sizeEq := evaluate_timeout_zeroClock_size program state next
    { next with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    safe peak stackMax zero run targetRun
  change next.localsSize = localsSize at sizeEq
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

end Flapjack.Compiler.Backend.DataSpace
