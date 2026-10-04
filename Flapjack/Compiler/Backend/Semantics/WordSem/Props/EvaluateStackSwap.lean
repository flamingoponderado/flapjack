import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.MustTerminate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.If
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Call

/-!
# `evaluate_stack_swap`

Assembly of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap` from its
per-constructor cases (`EvaluateStackSwap/*`) by the tagged HOL `evaluate_ind`,
as in the HOL proof.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

namespace EvaluateStackSwapWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapWitnesses

open EvaluateStackSwapWitnesses

/-- Exact HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`): for every
program and state, the result-dependent conclusion `stackSwapPost` (HOL's
`case evaluate (c,s) of ...`). Proved, as in HOL, by `evaluate_ind` from the
26 tagged per-constructor cases. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackSwap {width : Nat} [NeZero width] {C F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      stackSwapPost c s :=
  evaluate_ind (fun c s => stackSwapPost c s)
    ⟨fun s => evaluateStackSwap_Skip s,
     fun n names s => evaluateStackSwap_Alloc n names s,
     fun t1 t2 a o ws s => evaluateStackSwap_StoreConsts t1 t2 a o ws s,
     fun pri moves s => evaluateStackSwap_Move pri moves s,
     fun i s => evaluateStackSwap_Inst i s,
     fun v e s => evaluateStackSwap_Assign v e s,
     fun v name s => evaluateStackSwap_Get v name s,
     fun v e s => evaluateStackSwap_Set v e s,
     fun b dst src s => evaluateStackSwap_OpCurrHeap b dst src s,
     fun e v s => evaluateStackSwap_Store e v s,
     fun s => evaluateStackSwap_Tick s,
     fun p s ih => evaluateStackSwap_MustTerminate p s ih,
     fun c1 c2 s ih => evaluateStackSwap_Seq c1 c2 s ih,
     fun n ms s => evaluateStackSwap_Return n ms s,
     fun n s => evaluateStackSwap_Raise n s,
     fun k s => evaluateStackSwap_Break k s,
     fun k s => evaluateStackSwap_Continue k s,
     fun cmp r1 ri c1 c2 s ih => evaluateStackSwap_If cmp r1 ri c1 c2 s ih,
     fun names c exitNames s ih => evaluateStackSwap_Loop names c exitNames s ih,
     fun r l1 s => evaluateStackSwap_LocValue r l1 s,
     fun ptr len dptr dlen names s => evaluateStackSwap_Install ptr len dptr dlen names s,
     fun r1 r2 s => evaluateStackSwap_CodeBufferWrite r1 r2 s,
     fun r1 r2 s => evaluateStackSwap_DataBufferWrite r1 r2 s,
     fun fi p1 l1 p2 l2 names s => evaluateStackSwap_FFI fi p1 l1 p2 l2 names s,
     fun op v e s => evaluateStackSwap_ShareInst op v e s,
     fun ret dest args h s ih => evaluateStackSwap_Call ret dest args h s ih⟩

end WordSemStackEq

end Flapjack
