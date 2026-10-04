import Flapjack.Compiler.Backend.StackProps.EvaluateIoEventsMono

/-! Full original StackProps extra-clock event monotonicity
(stackPropsScript.sml:542–638), over the faithful native evaluator.
All original outcomes, including timeout, are retained. Local case helpers
are Flapjack-only proof factoring, with no independent HOL declaration. -/
namespace Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl
open EvaluateIoEventsMono StackSemMeasure

/-- Local non-timeout case; the final theorem must be unconditional. -/
theorem eventsPrefixOfNotTimeOut {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (notTimeOut : (evaluate (program, source)).1 ≠ some .timeOut) :
    (evaluate (program, source)).2.ffi.ioEvents <+:
      (evaluate (program, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rcases run : evaluate (program, source) with ⟨result, post⟩
  have boost := evaluateAddClock extra program source result post
    ⟨run, by simpa only [run] using notTimeOut⟩
  rw [boost]


/-- Local clock-free branch, including all possible result constructors. -/
theorem eventsPrefixOfClockFree {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (free : EvaluateAddClock.ClockFree (C := C) (F := F) program) :
    (evaluate (program, source)).2.ffi.ioEvents <+:
      (evaluate (program, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rcases run : evaluate (program, source) with ⟨result, post⟩
  rw [EvaluateAddClock.addClock_of_clockFree free source post result extra run]

/-- Local Seq suffix: any actual second run extends the first run's events. -/
theorem firstSeqPrefix {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    (evaluate (first, source)).2.ffi.ioEvents <+:
      (evaluate (.seq first second, source)).2.ffi.ioEvents := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : evaluate (first, source) with ⟨result, post⟩
  cases result with
  | none => exact evaluateIoEventsMono second post _ _ rfl
  | some value => exact List.prefix_refl _

/-- Local Loop suffix: exits/zero-clock preserve the body trace and reentry
extends it by the checked single-run theorem. -/
theorem bodyLoopPrefix {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) :
    (evaluate (body, source)).2.ffi.ioEvents <+:
      (evaluate (.loop body, source)).2.ffi.ioEvents := by
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : evaluate (body, source) with ⟨result, post⟩
  dsimp only
  split
  · split
    · exact List.prefix_refl _
    · exact evaluateIoEventsMono (.loop body) (decClock post) _ _ rfl
  · exact List.prefix_refl _

/-- Local returning Call suffix, with its actual source lookup/clock/callee
run guards. Return and exception continuations use the single-run theorem. -/
theorem returningCallPrefix {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (program : HolProg width)
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (found : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (result, post)) :
    post.ffi.ioEvents <+:
      (evaluate (.call (some (body, link, l1, l2)) dest handler, source)).2.ffi.ioEvents := by
  rw [evaluate_call]
  simp only [found, nonzero, if_false]
  rw [StackSemEvaluateClock.fixClockEvaluate, run]
  cases result with
  | none => exact List.prefix_refl _
  | some result =>
    cases result
    all_goals dsimp only
    all_goals first
      | exact List.prefix_refl _
      | (split <;> first | exact List.prefix_refl _ | exact evaluateIoEventsMono body post _ _ rfl)
      | (cases handler with
         | none => exact List.prefix_refl _
         | some entry =>
           rcases entry with ⟨handlerBody, hl1, hl2⟩
           dsimp only
           split <;> first | exact List.prefix_refl _ | exact evaluateIoEventsMono handlerBody post _ _ rfl)


/-- Local Seq induction factoring, with only the two genuine recursive
extra-clock hypotheses. The second is guarded by the actual first NONE run. -/
theorem extraClockSeq {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (first second : HolProg width) (source : StackSemStateFiniteExact width C F)
    (firstIH : (evaluate (first, source)).2.ffi.ioEvents <+:
      (evaluate (first, {source with clock := source.clock + extra})).2.ffi.ioEvents)
    (secondIH : ∀ middle : StackSemStateFiniteExact width C F,
      evaluate (first, source) = (none, middle) →
      (evaluate (second, middle)).2.ffi.ioEvents <+:
        (evaluate (second, {middle with clock := middle.clock + extra})).2.ffi.ioEvents) :
    (evaluate (.seq first second, source)).2.ffi.ioEvents <+:
      (evaluate (.seq first second, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rcases run : evaluate (first, source) with ⟨result, middle⟩
  by_cases timeout : result = some .timeOut
  · subst result
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, run]
    rw [run] at firstIH
    exact firstIH.trans (firstSeqPrefix first second _)
  · have boost := evaluateAddClock extra first source result middle ⟨run, timeout⟩
    rw [evaluate_seq, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluateClock.fixClockEvaluate, run, boost]
    cases result with
    | none => exact secondIH middle run
    | some value => exact List.prefix_refl _

/-- Local If induction factoring; native register reads do not observe clock. -/
theorem extraClockIf {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (comparison : Encoders.Asm.HolCmp) (register : Nat) (operand : Encoders.Asm.HolRegImm width)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F)
    (firstIH : (evaluate (first, source)).2.ffi.ioEvents <+:
      (evaluate (first, {source with clock := source.clock + extra})).2.ffi.ioEvents)
    (secondIH : (evaluate (second, source)).2.ffi.ioEvents <+:
      (evaluate (second, {source with clock := source.clock + extra})).2.ffi.ioEvents) :
    (evaluate (.ite comparison register operand first second, source)).2.ffi.ioEvents <+:
      (evaluate (.ite comparison register operand first second,
        {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rw [evaluate_ite, evaluate_ite]
  have firstRead : getVar register {source with clock := source.clock + extra} =
      getVar register source := rfl
  have secondRead : StackSemStateOps.getVarImm (Encoders.Asm.HolRegImm.toWordRegImm operand)
      {source with clock := source.clock + extra} =
      StackSemStateOps.getVarImm (Encoders.Asm.HolRegImm.toWordRegImm operand) source := by
    cases Encoders.Asm.HolRegImm.toWordRegImm operand <;> rfl
  rw [firstRead, secondRead]
  repeat' split
  all_goals first | exact List.prefix_refl _ | exact firstIH | exact secondIH

/-- Local Loop induction factoring. Clock-zero reentry uses the checked
body suffix law; positive reentry uses its source-guarded recursive IH. -/
theorem extraClockLoop {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (body : HolProg width) (source : StackSemStateFiniteExact width C F)
    (bodyIH : (evaluate (body, source)).2.ffi.ioEvents <+:
      (evaluate (body, {source with clock := source.clock + extra})).2.ffi.ioEvents)
    (reentryIH : ∀ (result : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (result, middle) → contLoop result = true → middle.clock ≠ 0 →
      (evaluate (.loop body, decClock middle)).2.ffi.ioEvents <+:
        (evaluate (.loop body, {decClock middle with clock := (decClock middle).clock + extra})).2.ffi.ioEvents) :
    (evaluate (.loop body, source)).2.ffi.ioEvents <+:
      (evaluate (.loop body, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rcases run : evaluate (body, source) with ⟨result, middle⟩
  by_cases timeout : result = some .timeOut
  · subst result
    rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, run]
    simp only [contLoop, Bool.false_eq_true, if_false, StackSemControl.exitLoop]
    rw [run] at bodyIH
    exact bodyIH.trans (bodyLoopPrefix body _)
  · have boost := evaluateAddClock extra body source result middle ⟨run, timeout⟩
    by_cases continues : contLoop result = true
    · by_cases zero : middle.clock = 0
      · have suffix := bodyLoopPrefix body {source with clock := source.clock + extra}
        rw [boost] at suffix
        rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, run]
        simp only [continues, if_true, zero]
        exact suffix
      · rw [evaluate_loop, evaluate_loop, StackSemEvaluateClock.fixClockEvaluate,
          StackSemEvaluateClock.fixClockEvaluate, run, boost]
        simp only [continues, if_true]
        rw [if_neg zero, if_neg (show middle.clock + extra ≠ 0 by omega),
          EvaluateAddClock.decClock_addClock middle extra zero]
        exact reentryIH result middle run continues zero
    · rw [evaluate_loop, evaluate_loop, StackSemEvaluateClock.fixClockEvaluate,
        StackSemEvaluateClock.fixClockEvaluate, run, boost]
      simp only [continues]
      exact List.prefix_refl _

/-- Local RawCall induction factoring. The only recursive premise concerns
an actual looked-up Seq body at a decremented, positive source clock. -/
theorem extraClockRawCall {width : Nat} [NeZero width] {C F : Type}
    (extra dest : Nat) (source : StackSemStateFiniteExact width C F)
    (calleeIH : ∀ (program body : HolProg width) (initial : HolProg width),
      sptLookup dest source.code = some program → destSeq program = some (initial, body) →
      source.clock ≠ 0 →
      (evaluate (body, decClock source)).2.ffi.ioEvents <+:
        (evaluate (body, {decClock source with clock := (decClock source).clock + extra})).2.ffi.ioEvents) :
    (evaluate (.rawCall dest, source)).2.ffi.ioEvents <+:
      (evaluate (.rawCall dest, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rw [evaluate_rawCall, evaluate_rawCall]
  rcases found : sptLookup dest source.code with _ | program
  · dsimp only; exact List.prefix_refl _
  · dsimp only
    rcases sequence : destSeq program with _ | ⟨initial, body⟩
    · dsimp only; exact List.prefix_refl _
    · dsimp only
      by_cases zero : source.clock = 0
      · rw [if_pos zero]
        have suffix := evaluateIoEventsMono (.rawCall dest)
          {source with clock := source.clock + extra} _ _ rfl
        change source.ffi.ioEvents <+:
          (evaluate (.rawCall dest, {source with clock := source.clock + extra})).2.ffi.ioEvents at suffix
        rw [evaluate_rawCall] at suffix
        simpa only [found, sequence, emptyEnv] using suffix
      · rw [if_neg zero, if_neg (show source.clock + extra ≠ 0 by omega),
          EvaluateAddClock.decClock_addClock source extra zero]
        have eventsPrefix := calleeIH program body initial found sequence zero
        rcases run : evaluate (body, decClock source) with ⟨result, post⟩
        rcases boostedRun : evaluate (body,
          {decClock source with clock := (decClock source).clock + extra}) with ⟨boostedResult, boostedPost⟩
        rw [run, boostedRun] at eventsPrefix
        dsimp only
        split <;> split <;> exact eventsPrefix

/-- Local returning Call case. Actual source lookup/run guards and genuine
callee/continuation induction hypotheses discharge both timeout propagation
and return/exception continuation traces. -/
theorem extraClockReturningCall {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (body : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F)
    (found : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (calleeIH : (evaluate (program, decClock (setVar link (.loc l1 l2) source))).2.ffi.ioEvents <+:
      (evaluate (program, {decClock (setVar link (.loc l1 l2) source) with
        clock := (decClock (setVar link (.loc l1 l2) source)).clock + extra})).2.ffi.ioEvents)
    (continuationIH : ∀ (result : Option (StackSemResult width))
      (post : StackSemStateFiniteExact width C F) (continuation : HolProg width),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (result, post) →
      (evaluate (continuation, post)).2.ffi.ioEvents <+:
        (evaluate (continuation, {post with clock := post.clock + extra})).2.ffi.ioEvents) :
    (evaluate (.call (some (body, link, l1, l2)) dest handler, source)).2.ffi.ioEvents <+:
      (evaluate (.call (some (body, link, l1, l2)) dest handler,
        {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  have setClock : setVar link (.loc l1 l2) {source with clock := source.clock + extra} =
      {setVar link (.loc l1 l2) source with
        clock := (setVar link (.loc l1 l2) source).clock + extra} := rfl
  have decClockBoost : decClock (setVar link (.loc l1 l2)
      {source with clock := source.clock + extra}) =
      {decClock (setVar link (.loc l1 l2) source) with
        clock := (decClock (setVar link (.loc l1 l2) source)).clock + extra} := by
    rw [setClock]
    exact EvaluateAddClock.decClock_addClock (setVar link (.loc l1 l2) source) extra nonzero
  rcases run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with ⟨result, post⟩
  by_cases timeout : result = some .timeOut
  · subst result
    rw [evaluate_call]
    simp only [found, nonzero, if_false]
    rw [StackSemEvaluateClock.fixClockEvaluate, run]
    dsimp only
    rw [run] at calleeIH
    have suffix := returningCallPrefix body link l1 l2 dest handler program
      {source with clock := source.clock + extra}
      (evaluate (program, decClock (setVar link (.loc l1 l2)
        {source with clock := source.clock + extra}))).2
      (evaluate (program, decClock (setVar link (.loc l1 l2)
        {source with clock := source.clock + extra}))).1
      found (by dsimp only; omega) rfl
    rw [decClockBoost] at suffix
    exact calleeIH.trans suffix
  · have boost := evaluateAddClock extra program
      (decClock (setVar link (.loc l1 l2) source)) result post ⟨run, timeout⟩
    rw [evaluate_call, evaluate_call]
    simp only [found, nonzero, if_false]
    rw [if_neg (show source.clock + extra ≠ 0 by omega),
      StackSemEvaluateClock.fixClockEvaluate, StackSemEvaluateClock.fixClockEvaluate,
      decClockBoost, run, boost]
    cases result with
    | none => exact List.prefix_refl _
    | some value =>
      cases value
      all_goals dsimp only
      all_goals first
        | exact List.prefix_refl _
        | (split <;> first
            | exact List.prefix_refl _
            | exact continuationIH _ post body run)
        | (cases handler with
           | none => exact List.prefix_refl _
           | some entry =>
             rcases entry with ⟨handlerBody, hl1, hl2⟩
             dsimp only
             split <;> first
               | exact List.prefix_refl _
               | exact continuationIH _ post handlerBody run)

/-- Local successful-lookup positive-clock TailCall case; bad function
return changes only the result, so every native callee trace is retained. -/
theorem extraClockTailCall {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (dest : Sum Nat Nat) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F)
    (found : findCode dest source.regs source.code = some program)
    (nonzero : source.clock ≠ 0)
    (calleeIH : (evaluate (program, decClock source)).2.ffi.ioEvents <+:
      (evaluate (program, {decClock source with clock := (decClock source).clock + extra})).2.ffi.ioEvents) :
    (evaluate (.call none dest none, source)).2.ffi.ioEvents <+:
      (evaluate (.call none dest none, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rw [evaluate_call, evaluate_call]
  simp only [found, nonzero, if_false]
  rw [if_neg (show source.clock + extra ≠ 0 by omega),
    StackSemEvaluateClock.fixClockEvaluate, StackSemEvaluateClock.fixClockEvaluate,
    EvaluateAddClock.decClock_addClock source extra nonzero]
  rcases run : evaluate (program, decClock source) with ⟨result, post⟩
  rcases boostedRun : evaluate (program,
    {decClock source with clock := (decClock source).clock + extra}) with ⟨boostedResult, boostedPost⟩
  rw [run, boostedRun] at calleeIH
  dsimp only
  split <;> split <;> exact calleeIH

/-- Local JumpLower induction factoring; false comparisons and failed
lookups are clock-free, while zero clock uses native single-run monotonicity. -/
theorem extraClockJumpLower {width : Nat} [NeZero width] {C F : Type}
    (extra r1 r2 dest : Nat) (source : StackSemStateFiniteExact width C F)
    (calleeIH : ∀ program : HolProg width,
      findCode (.inl dest) source.regs source.code = some program → source.clock ≠ 0 →
      (evaluate (program, decClock source)).2.ffi.ioEvents <+:
        (evaluate (program, {decClock source with clock := (decClock source).clock + extra})).2.ffi.ioEvents) :
    (evaluate (.jumpLower r1 r2 dest, source)).2.ffi.ioEvents <+:
      (evaluate (.jumpLower r1 r2 dest, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  rw [evaluate_jumpLower, evaluate_jumpLower]
  have read1 : getVar r1 {source with clock := source.clock + extra} = getVar r1 source := rfl
  have read2 : getVar r2 {source with clock := source.clock + extra} = getVar r2 source := rfl
  rw [read1, read2]
  rcases value1 : getVar r1 source with _ | ⟨x⟩ | ⟨l1,l2⟩ <;>
    rcases value2 : getVar r2 source with _ | ⟨y⟩ | ⟨m1,m2⟩ <;>
    dsimp only
  all_goals try exact List.prefix_refl _
  by_cases lower : Encoders.Asm.wordCmpHOL .lower x y = true
  · rw [if_pos lower, if_pos lower]
    rcases found : findCode (.inl dest) source.regs source.code with _ | program
    · dsimp only; exact List.prefix_refl _
    · dsimp only
      by_cases zero : source.clock = 0
      · rw [if_pos zero]
        have suffix := evaluateIoEventsMono (.jumpLower r1 r2 dest)
          {source with clock := source.clock + extra} _ _ rfl
        change source.ffi.ioEvents <+:
          (evaluate (.jumpLower r1 r2 dest, {source with clock := source.clock + extra})).2.ffi.ioEvents at suffix
        rw [evaluate_jumpLower, read1, read2] at suffix
        simpa only [value1, value2, lower, if_true, found, emptyEnv] using suffix
      · rw [if_neg zero, if_neg (show source.clock + extra ≠ 0 by omega),
          EvaluateAddClock.decClock_addClock source extra zero]
        have eventsPrefix := calleeIH program found zero
        rcases run : evaluate (program, decClock source) with ⟨result, post⟩
        rcases boostedRun : evaluate (program,
          {decClock source with clock := (decClock source).clock + extra}) with ⟨boostedResult, boostedPost⟩
        rw [run, boostedRun] at eventsPrefix
        dsimp only
        split <;> split <;> exact eventsPrefix
  · rw [if_neg lower, if_neg lower]

/-- Local full native evaluator induction; no independent HOL declaration.
Every recursive hypothesis is derived from the original clock-first measure. -/
private theorem extraClockMeasure {width : Nat} [NeZero width] {C F : Type} (extra : Nat) :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      (evaluate (program, source)).2.ffi.ioEvents <+:
        (evaluate (program, {source with clock := source.clock + extra})).2.ffi.ioEvents := by
  intro measure
  induction measure using EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source sameMeasure
  subst sameMeasure
  cases program
  all_goals first
    | exact eventsPrefixOfClockFree extra _ source (EvaluateAddClock.clockFree_of_ctor _ rfl)
    | skip
  case inst instruction =>
    exact eventsPrefixOfClockFree extra _ source (EvaluateAddClock.clockFree_inst instruction)
  case alloc register =>
    exact eventsPrefixOfClockFree extra _ source (EvaluateAddClock.clockFree_alloc register)
  case storeConsts t1 t2 stub =>
    exact eventsPrefixOfClockFree extra _ source (EvaluateAddClock.clockFree_storeConsts t1 t2 stub)
  case tick =>
    rw [evaluate_tick, evaluate_tick]
    split <;> split <;> exact List.prefix_refl _
  case shMemOp operation register address =>
    cases address with
    | addr a offset =>
    rw [evaluate_shMemOp, evaluate_shMemOp,
      StackPropsExpressionClock.wordExpWithClock source _ (source.clock + extra)]
    rcases value : StackSemExpressions.wordExp source (.op .add [.var a, .const offset]) with _ | location
    · dsimp only; exact List.prefix_refl _
    · dsimp only
      by_cases zero : source.clock = 0
      · rw [if_pos zero]
        have suffix := evaluateIoEventsMono (.shMemOp operation register (.addr a offset))
          {source with clock := source.clock + extra} _ _ rfl
        change source.ffi.ioEvents <+:
          (evaluate (.shMemOp operation register (.addr a offset),
            {source with clock := source.clock + extra})).2.ffi.ioEvents at suffix
        rw [evaluate_shMemOp, StackPropsExpressionClock.wordExpWithClock source _ (source.clock + extra)] at suffix
        simpa only [value, emptyEnv] using suffix
      · rw [if_neg zero, if_neg (show source.clock + extra ≠ 0 by omega),
          EvaluateAddClock.decClock_addClock source extra zero,
          StackPropsSharedMemoryClock.shMemOpWithClock operation register location
            (decClock source) ((decClock source).clock + extra)]
        rcases StackSemShMem.shMemOp operation register location (decClock source) with ⟨result, post⟩
        exact List.prefix_refl _
  case seq first second =>
    apply extraClockSeq extra first second source
    · exact ih _ (seq_first_measure_lt first second source) first source rfl
    · intro middle run
      have smaller := seq_second_measure_lt first second source (evaluate (first,source))
      rw [StackSemEvaluateClock.fixClockEvaluate, run] at smaller
      exact ih _ smaller second middle rfl
  case ite comparison register operand first second =>
    exact extraClockIf extra comparison register operand first second source
      (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl)
      (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl)
  case loop body =>
    apply extraClockLoop extra body source
    · exact ih _ (loop_body_measure_lt body source) body source rfl
    · intro result middle run _ nonzero
      have smaller := loop_reentry_measure_lt body source (evaluate (body,source))
        (by rw [StackSemEvaluateClock.fixClockEvaluate, run]; exact nonzero)
      rw [StackSemEvaluateClock.fixClockEvaluate, run] at smaller
      exact ih _ smaller (.loop body) (decClock middle) rfl
  case rawCall dest =>
    apply extraClockRawCall extra dest source
    intro program body initial _ _ nonzero
    exact ih _ (callee_measure_lt body (.rawCall dest) source nonzero) body (decClock source) rfl
  case jumpLower r1 r2 dest =>
    apply extraClockJumpLower extra r1 r2 dest source
    intro program _ nonzero
    exact ih _ (callee_measure_lt program (.jumpLower r1 r2 dest) source nonzero)
      program (decClock source) rfl
  case call ret dest handler =>
    cases ret with
    | none =>
      rcases found : findCode dest source.regs source.code with _ | program
      · rw [evaluate_call, evaluate_call]
        simp only [found]
        exact List.prefix_refl _
      · cases handler with
        | some entry =>
          rw [evaluate_call, evaluate_call]
          simp only [found]
          exact List.prefix_refl _
        | none =>
          by_cases zero : source.clock = 0
          · rw [evaluate_call]
            simp only [found, zero, if_true]
            have suffix := evaluateIoEventsMono (.call none dest none)
              {source with clock := source.clock + extra} _ _ rfl
            simpa only [zero, emptyEnv, evaluate] using suffix
          · exact extraClockTailCall extra dest program source found zero
              (ih _ (callee_measure_lt program (.call none dest none) source zero)
                program (decClock source) rfl)
    | some entry =>
      rcases entry with ⟨body, link, l1, l2⟩
      rcases found : findCode dest (source.regs.eraseEq link) source.code with _ | program
      · rw [evaluate_call, evaluate_call]
        simp only [found]
        exact List.prefix_refl _
      · by_cases zero : source.clock = 0
        · rw [evaluate_call]
          simp only [found, zero, if_true]
          have suffix := evaluateIoEventsMono (.call (some (body, link, l1, l2)) dest handler)
            {source with clock := source.clock + extra} _ _ rfl
          simpa only [zero, emptyEnv, evaluate] using suffix
        · apply extraClockReturningCall extra body link l1 l2 dest handler program source found zero
          · exact ih _ (callee_measure_lt program
              (.call (some (body, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) source) zero)
              program (decClock (setVar link (.loc l1 l2) source)) rfl
          · intro result post continuation run
            have smaller := call_continuation_measure_lt continuation
              (.call (some (body, link, l1, l2)) dest handler)
              source link l1 l2 (evaluate (program, decClock (setVar link (.loc l1 l2) source))) zero
            rw [StackSemEvaluateClock.fixClockEvaluate, run] at smaller
            exact ih _ smaller continuation post rfl

/-- Canonical codec witness for the actual imported native state owner. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original `evaluate_add_clock_io_events_mono` (542–638), with
HOL's free `extra` universally closed. The statement is unconditional and
retains arbitrary native programs/states and every result, including timeout.
The clock-first induction derives all recursive obligations; checked native
single-run prefixes handle further execution after a timeout. The evaluator
closure inherits reviewed reals_as_rational_cuts (SOUNDNESS item 8); this
event theorem does not assert FP numerical parity. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateAddClockIoEventsMono {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F) :
    (evaluate (program, source)).2.ffi.ioEvents <+:
      (evaluate (program, {source with clock := source.clock + extra})).2.ffi.ioEvents :=
  extraClockMeasure extra (stackSemMeasure program source) program source rfl

end Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
