import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.RecursiveCalls

namespace Flapjack.WordToStackProofs.AllocArgs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

/-- Full original arbitrary-program allocation-argument theorem. All recursive
case hypotheses are discharged internally, with arbitrary threaded bitmap and
frame inputs; the only source premise is the original false-performance guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArg {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) : allocArg (compNative conf perf program bs frame).1 := by
  cases program with
  | skip => exact wordToStackAllocArgSkip conf perf bs frame plain
  | move _ _ => exact wordToStackAllocArgMove conf perf _ _ bs frame plain
  | inst _ => exact wordToStackAllocArgInst conf perf _ bs frame plain
  | assign _ _ => exact wordToStackAllocArgAssign conf perf _ _ bs frame plain
  | get _ _ => exact wordToStackAllocArgGet conf perf _ _ bs frame plain
  | set _ _ => exact wordToStackAllocArgSet conf perf _ _ bs frame plain
  | store _ _ => exact wordToStackAllocArgStore conf perf _ _ bs frame plain
  | alloc _ _ => exact wordToStackAllocArgAlloc conf perf _ _ bs frame plain
  | storeConsts _ _ _ _ _ => exact wordToStackAllocArgStoreConsts conf perf _ _ _ _ _ bs frame plain
  | raise _ => exact wordToStackAllocArgRaise conf perf _ bs frame plain
  | «return» _ _ => exact wordToStackAllocArgReturn conf perf _ _ bs frame plain
  | «break» _ => exact wordToStackAllocArgBreak conf perf _ bs frame plain
  | «continue» _ => exact wordToStackAllocArgContinue conf perf _ bs frame plain
  | tick => exact wordToStackAllocArgTick conf perf bs frame plain
  | opCurrHeap _ _ _ => exact wordToStackAllocArgOpCurrHeap conf perf _ _ _ bs frame plain
  | locValue _ _ => exact wordToStackAllocArgLocValue conf perf _ _ bs frame plain
  | install _ _ _ _ _ => exact wordToStackAllocArgInstall conf perf _ _ _ _ _ bs frame plain
  | codeBufferWrite _ _ => exact wordToStackAllocArgCodeBufferWrite conf perf _ _ bs frame plain
  | dataBufferWrite _ _ => exact wordToStackAllocArgDataBufferWrite conf perf _ _ bs frame plain
  | ffi _ _ _ _ _ _ => exact wordToStackAllocArgFfi conf perf _ _ _ _ _ _ bs frame plain
  | shareInst _ _ _ => exact wordToStackAllocArgShareInst conf perf _ _ _ bs frame plain
  | mustTerminate body =>
      exact wordToStackAllocArgMustTerminate conf perf body bs frame plain
        (fun bs frame plain => wordToStackAllocArg conf perf body bs frame plain)
  | loop liveIn body liveOut =>
      exact wordToStackAllocArgLoop conf perf liveIn liveOut body bs frame plain
        (fun bs frame plain => wordToStackAllocArg conf perf body bs frame plain)
  | seq first second =>
      exact wordToStackAllocArgSeq conf perf first second bs frame plain
        (fun bs frame plain => wordToStackAllocArg conf perf first bs frame plain)
        (fun bs frame plain => wordToStackAllocArg conf perf second bs frame plain)
  | ite cmp reg ri first second =>
      exact wordToStackAllocArgIf conf perf cmp reg ri first second bs frame plain
        (fun bs frame plain => wordToStackAllocArg conf perf first bs frame plain)
        (fun bs frame plain => wordToStackAllocArg conf perf second bs frame plain)
  | call returns dest args handler =>
      cases returns with
      | none => exact wordToStackAllocArgCallTail conf perf dest args handler bs frame plain
      | some record =>
          match hRet : record with
          | (values,live,retCode,l1,l2) =>
              cases handler with
              | none =>
                  exact wordToStackAllocArgCallReturn conf perf values live retCode l1 l2
                    dest args bs frame plain
                    (fun bs frame plain => wordToStackAllocArg conf perf retCode bs frame plain)
              | some record =>
                  match hHandle : record with
                  | (handleValue,handleCode,h1,h2) =>
                      exact wordToStackAllocArgCallHandler conf perf values live retCode handleCode
                        l1 l2 handleValue h1 h2 dest args bs frame plain
                        (fun bs frame plain => wordToStackAllocArg conf perf retCode bs frame plain)
                        (fun bs frame plain => wordToStackAllocArg conf perf handleCode bs frame plain)
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.WordToStackProofs.AllocArgs
