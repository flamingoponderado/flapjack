module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackLocalsSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.StackFrameSizeRel
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.FindCodeSize
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-!
# Stack-frame-size replacement under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2566`
`evaluate_swap_stack_frame_sizes_aux`, together with `evaluate_swap_local_sizes`
(`:2798`), `evaluate_swap_stack_frame_sizes` (`:2826`) and the consequences
`evaluate_stack_frame_sizes_FST` (`:2852`) and `evaluate_stack_frame_sizes_ffi`
(`:2862`).

The step lemmas below are the induction's cases. They are Flapjack
infrastructure toward the port of `evaluate_swap_stack_frame_sizes_aux`; they
carry no `@[hol]` tag of their own.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataSem

/-- The stack-frame-size replacement property for one program and state: the
    outcome is preserved when the locals size, the stack (up to frame-size
    agreement) and the stack-frame sizes are replaced, with the resource
    observations and the resulting frame-size map free. -/
private def StackFrameSwapAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F),
    evaluate program state = (res, next) →
    ∀ (xs : List Stack) (lsz : Option Nat) (sfs : Spt Nat),
      List.Forall₂ stackFrameSizeRel state.stack xs →
      ∃ (xs' : List Stack) (lss : Option Nat) (smx : Option Nat) (safe : Bool) (peak : Nat)
        (sfs' : Spt Nat),
        evaluate program { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } =
          (res, { next with
            localsSize := lss
            safeForSpace := safe
            stack := xs'
            stackFrameSizes := sfs'
            stackMax := smx
            peakHeapLength := peak }) ∧
        List.Forall₂ stackFrameSizeRel next.stack xs'

/-- Frame-size agreement is reflexive. Flapjack infrastructure toward the port
    of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem forall₂_stackFrameSizeRel_refl (frames : List Stack) :
    List.Forall₂ stackFrameSizeRel frames frames := by
  induction frames with
  | nil => exact List.Forall₂.nil
  | cons frame rest ih =>
    refine List.Forall₂.cons ?_ ih
    cases frame <;> simp [stackFrameSizeRel]

/-- The frame-size map after a primitive application: an installation primitive
    clears it and every other operation leaves it unchanged. This is Flapjack
    infrastructure for the port of HOL `evaluate_swap_stack_frame_sizes_aux`;
    it renders the dispatcher's `if op = Install then LN else sfs` branch as a
    pattern match, because `ClosLang.Op` has no decidable equality. -/
private def installSfsMap (op : ClosLang.Op) (sfs : Spt Nat) : Spt Nat :=
  match op with
  | .install => .ln
  | _ => sfs

/-- Unfolding lemma for the installation frame-size map. -/
private theorem installSfsMap_unfold (op : ClosLang.Op) (sfs : Spt Nat) :
    installSfsMap op sfs = (match op with | .install => (.ln : Spt Nat) | _ => sfs) := rfl

/-- The `Skip` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_skip {C F : Type} (state : State C F) :
    StackFrameSwapAt (.skip : DataLang.Prog) state := by
  intro res next run xs lsz sfs related
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
    ⟨by simp [evaluate], related⟩⟩

/-- The `Move` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_move {C F : Type} (dest src : Nat) (state : State C F) :
    StackFrameSwapAt (.move dest src) state := by
  intro res next run xs lsz sfs related
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, read], related⟩⟩
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs, ?_, ?_⟩
    · simp [evaluate, read, setVar]
    · simpa [setVar] using related

/-- The `Tick` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_tick {C F : Type} (state : State C F) :
    StackFrameSwapAt (.tick : DataLang.Prog) state := by
  intro res next run xs lsz sfs related
  by_cases zero : state.clock = 0
  · simp only [evaluate, zero, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨[], some 0, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs, ?_, ?_⟩
    · simp [evaluate, zero, timeoutError, flushState]
    · simp [flushState]
  · simp only [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs, ?_, ?_⟩
    · simp [evaluate, zero, decClock]
    · simpa [decClock] using related

/-- The `MakeSpace` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : StackFrameSwapAt (.makeSpace amount names) state := by
  intro res next run xs lsz sfs related
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, cut], related⟩⟩
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    let swapped : State C F :=
      { state with locals := env, localsSize := lsz, stack := xs, stackFrameSizes := sfs }
    let target := addSpace swapped amount
    refine ⟨xs, lsz, state.stackMax, target.safeForSpace, target.peakHeapLength, sfs, ?_, ?_⟩
    · simp only [evaluate, cut]
      rfl
    · simpa [addSpace] using related

/-- The `Return` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_return {C F : Type} (names : List Nat) (state : State C F) :
    StackFrameSwapAt (.return names) state := by
  intro res next run xs lsz sfs related
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, read], related⟩⟩
  | some values =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨xs, some 0, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs, ?_, ?_⟩
    · simp [evaluate, read, flushState]
    · simpa [flushState] using related

/-- The `If` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : StackFrameSwapAt yes state) (noIH : StackFrameSwapAt no state) :
    StackFrameSwapAt (.ifThenElse name yes no) state := by
  intro res next run xs lsz sfs related
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, read], related⟩⟩
  | some value =>
    by_cases yesValue : isBool true value
    · have branch : evaluate yes state = (res, next) := by
        simpa [evaluate, read, yesValue] using run
      simpa [evaluate, read, yesValue] using yesIH res next branch xs lsz sfs related
    · by_cases noValue : isBool false value
      · have branch : evaluate no state = (res, next) := by
          simpa [evaluate, read, yesValue, noValue] using run
        simpa [evaluate, read, yesValue, noValue] using noIH res next branch xs lsz sfs related
      · simp only [evaluate, read, yesValue, noValue, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
          ⟨by simp [evaluate, read, yesValue, noValue], related⟩⟩

/-- A sequential composition whose first half has stopped returns the first
    half's result. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem seq_some {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (stopped : Result (List DataSem.Value) DataSem.Value) (next : State C F)
    (run : evaluate first state = (some stopped, next)) :
    evaluate (.seq first second) state = (some stopped, next) := by
  have bound : next.clock ≤ state.clock := by simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- A sequential composition whose first half continues evaluates the second
    half at the first half's result state. Flapjack infrastructure toward the
    port of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem seq_none {C F : Type} (first second : DataLang.Prog) (state mid : State C F)
    (run : evaluate first state = (none, mid)) :
    evaluate (.seq first second) state = evaluate second mid := by
  have bound : mid.clock ≤ state.clock := by
    simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- The `Seq` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : StackFrameSwapAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → StackFrameSwapAt second mid) :
    StackFrameSwapAt (.seq first second) state := by
  intro res next run xs lsz sfs related
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    have midClock : mid.clock ≤ state.clock := by
      simpa only [firstRun] using evaluate_clock_le first state
    cases outcome with
    | some stopped =>
      have clamp : fixClock state (evaluate first state) = (some stopped, mid) := by
        rw [fixClockEvaluate, firstRun]
      have hres : res = some stopped := by
        have h := congrArg Prod.fst run
        simpa only [evaluate, clamp] using h.symm
      have hnext : next = mid := by
        have h := congrArg Prod.snd run
        simpa only [evaluate, clamp] using h.symm
      rw [hres, hnext]
      obtain ⟨xs1, lss, smx, safe, peak, sfs1, firstTarget, rel⟩ :=
        firstIH (some stopped) mid firstRun xs lsz sfs related
      refine ⟨xs1, lss, smx, safe, peak, sfs1, ?_, rel⟩
      rw [seq_some first second _ stopped _ firstTarget]
    | none =>
      have secondRun : evaluate second mid = (res, next) := by
        have clamp : fixClock state (evaluate first state) = (none, mid) := by
          rw [fixClockEvaluate, firstRun]
        simpa only [evaluate, clamp] using run
      obtain ⟨xs1, lss1, smx1, safe1, peak1, sfs1, firstTarget, rel1⟩ :=
        firstIH none mid firstRun xs lsz sfs related
      obtain ⟨xs2, lss2, smx2, safe2, peak2, sfs2, secondTarget, rel2⟩ :=
        secondIH mid midClock res next secondRun xs1 lss1 sfs1 rel1
      obtain ⟨mx', safe', peak', moved⟩ :=
        evaluate_stackSafePeakSwap smx1 safe1 _ _ _ peak1 second secondTarget
      refine ⟨xs2, lss2, mx', safe', peak', sfs2, ?_, rel2⟩
      rw [seq_none first second _ _ firstTarget]
      exact moved

/-- The `Assign` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    StackFrameSwapAt (.assign dest op names live) state := by
  intro res next run xs lsz sfs related
  by_cases needs : (DataLang.opRequiresNames op == live.isNone) = true
  · simp only [evaluate, needs, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, needs], related⟩⟩
  · have needsFalse : (DataLang.opRequiresNames op == live.isNone) = false := by
      simpa using needs
    simp only [evaluate, needsFalse] at run
    cases vars : DataSem.getVars names state.locals with
    | none =>
      simp only [vars, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
        ⟨by simp [evaluate, needsFalse, vars], related⟩⟩
    | some values =>
      simp only [vars] at run
      cases cut : cutStateOpt live state with
      | none =>
        simp only [cut, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        have cutSwap :
            cutStateOpt live { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } =
              none := by
          rw [cutStateOpt_withFrameFields, cut]
          rfl
        exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
          ⟨by simp [evaluate, needsFalse, vars, cutSwap], related⟩⟩
      | some mid =>
        simp only [cut] at run
        have cutSwap :
            cutStateOpt live { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } =
              some { mid with localsSize := lsz, stack := xs, stackFrameSizes := sfs } := by
          rw [cutStateOpt_withFrameFields, cut]
          rfl
        have midStack : mid.stack = state.stack := cutStateOpt_stack live state mid cut
        cases app : doApp op values mid with
        | err error =>
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          have appRun := doApp_err_lssStackFrameSwap op values mid error lsz xs sfs app
          refine ⟨[], some 0, mid.stackMax, (flushState true (installSfs op mid)).safeForSpace,
            mid.peakHeapLength, sfs, ?_, ?_⟩
          · simp [evaluate, needsFalse, vars, cutSwap, appRun, flushState, installSfs]
          · simp [flushState]
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          have control := doApp_const op values mid value last app
          obtain ⟨safe, peak, smx, appRun⟩ :=
            doApp_lssStackFrameSwap op values mid value last lsz xs sfs app
          refine ⟨xs, lsz, smx, (installSfs op { last with
              localsSize := lsz
              stack := xs
              stackFrameSizes := installSfsMap op sfs
              stackMax := smx
              safeForSpace := safe
              peakHeapLength := peak }).safeForSpace, peak,
            installSfsMap op sfs, ?_, ?_⟩
          · simp only [evaluate, needsFalse, vars, cutSwap, appRun, setVar, installSfs]
            rw [if_neg (by decide)]
            rw [installSfsMap_unfold]
            rfl
          · simpa [setVar, installSfs, control.1.trans midStack] using related

/-- Frame-size agreement decides the exception jump: when the original stack
    jumps to no frame, so does a related stack at the same handler index.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem jumpExc_none_of_related {C F : Type} (state other : State C F)
    (handlerEq : other.handler = state.handler)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : jumpExc state = none) : jumpExc other = none := by
  cases otherJump : jumpExc other with
  | none => rfl
  | some jumped =>
    obtain ⟨_, n, e, ls, xs1, lastNO, _⟩ := jumpExcImp other jumped otherJump
    rw [handlerEq] at lastNO
    have hlen : state.stack.length = other.stack.length := related.length_eq
    have hltS : state.handler < state.stack.length := by omega
    have relLast := listRelLastN stackFrameSizeRel state.stack other.stack (state.handler + 1)
      ⟨by omega, related⟩
    rw [lastNO] at relLast
    obtain ⟨frame, rest, frameRel, _, lastEq⟩ := List.forall₂_cons_right_iff.mp relLast
    cases frame with
    | env size env => simp [stackFrameSizeRel] at frameRel
    | exc size env handler =>
      have jumpSome : jumpExc state =
          some { state with
                  handler := handler
                  locals := env
                  stack := rest
                  localsSize := size } := by
        unfold jumpExc
        rw [if_pos hltS, ← wordSemLastN_eq_drop, lastEq]
      rw [jumpSome] at run
      cases run

/-- The `Raise` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_raise {C F : Type} (name : Nat) (state : State C F) :
    StackFrameSwapAt (.raise name) state := by
  intro res next run xs lsz sfs related
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
      ⟨by simp [evaluate, read], related⟩⟩
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp only [evaluate, read, jump, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have jumpSwap := jumpExc_none_of_related state
        { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } rfl related jump
      refine ⟨xs, lsz, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs, ?_, ?_⟩
      · simp only [evaluate, read, jumpSwap]
        rfl
      · simpa using related
    | some jumped =>
      simp only [evaluate, read, jump, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨hlt, n, e, ls, xs1, lastN, jumpedEq⟩ := jumpExcImp state jumped jump
      have lenEq : xs.length = state.stack.length := related.length_eq.symm
      have hltX : state.handler < xs.length := by omega
      have relLast := listRelLastN stackFrameSizeRel state.stack xs (state.handler + 1)
        ⟨by omega, related⟩
      rw [lastN] at relLast
      obtain ⟨frame, rest, frameRel, restRel, lastX⟩ :=
        List.forall₂_cons_left_iff.mp relLast
      cases frame with
      | env size env => simp [stackFrameSizeRel] at frameRel
      | exc size env handler =>
        simp only [stackFrameSizeRel] at frameRel
        obtain ⟨envEq, handlerEq⟩ := frameRel
        subst envEq
        subst handlerEq
        subst jumpedEq
        have jumpSwap :
            jumpExc { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } =
              some { state with
                      localsSize := size
                      stack := rest
                      stackFrameSizes := sfs
                      handler := n
                      locals := e } := by
          unfold jumpExc
          rw [if_pos hltX, ← wordSemLastN_eq_drop, lastX]
        refine ⟨rest, size, state.stackMax, state.safeForSpace, state.peakHeapLength, sfs,
          ?_, ?_⟩
        · simp only [evaluate, read, jumpSwap]
        · simpa using restRel

end Flapjack.Compiler.Backend.DataProps
