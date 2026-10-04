import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions

namespace Flapjack.WordToStackProofs.RegisterBoundCompiler
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

open Flapjack.WordToStackProofs.RegisterBoundFlat
open Flapjack.WordToStackProofs.RegisterBoundRecursive
open Flapjack.WordToStackProofs.RegisterBoundInstructions

/-- Entire original arbitrary-program register-bound theorem over actual native
compilation. All proper-subprogram hypotheses are discharged internally at the
actual threaded bitmap states. The premises are exactly the source conventions,
original minimum frame bound and false-performance guard; no target result or
safety predicate is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackRegBound {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (conventions : postAllocConventionsHOL frame.1 program = true)
    (room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf program bs frame).1 (frame.1 + 2) := by
  cases program with
  | skip => exact wordToStackRegBoundSkip conf perf bs frame conventions room plain
  | move _ _ => exact wordToStackRegBoundMove conf perf _ _ bs frame conventions room plain
  | inst _ => exact wordToStackRegBoundInst conf perf _ bs frame conventions room plain
  | assign _ _ => exact wordToStackRegBoundAssign conf perf _ _ bs frame conventions room plain
  | get _ _ => exact wordToStackRegBoundGet conf perf _ _ bs frame conventions room plain
  | set _ _ => exact wordToStackRegBoundSet conf perf _ _ bs frame conventions room plain
  | store _ _ => exact wordToStackRegBoundStore conf perf _ _ bs frame conventions room plain
  | alloc _ _ => exact wordToStackRegBoundAlloc conf perf _ _ bs frame conventions room plain
  | storeConsts _ _ _ _ _ => exact wordToStackRegBoundStoreConsts conf perf _ _ _ _ _ bs frame conventions room plain
  | raise _ => exact wordToStackRegBoundRaise conf perf _ bs frame conventions room plain
  | «return» _ _ => exact wordToStackRegBoundReturn conf perf _ _ bs frame conventions room plain
  | «break» _ => exact wordToStackRegBoundBreak conf perf _ bs frame conventions room plain
  | «continue» _ => exact wordToStackRegBoundContinue conf perf _ bs frame conventions room plain
  | tick => exact wordToStackRegBoundTick conf perf bs frame conventions room plain
  | opCurrHeap _ _ _ => exact wordToStackRegBoundOpCurrHeap conf perf _ _ _ bs frame conventions room plain
  | locValue _ _ => exact wordToStackRegBoundLocValue conf perf _ _ bs frame conventions room plain
  | install _ _ _ _ _ => exact wordToStackRegBoundInstall conf perf _ _ _ _ _ bs frame conventions room plain
  | codeBufferWrite _ _ => exact wordToStackRegBoundCodeBufferWrite conf perf _ _ bs frame conventions room plain
  | dataBufferWrite _ _ => exact wordToStackRegBoundDataBufferWrite conf perf _ _ bs frame conventions room plain
  | ffi _ _ _ _ _ _ => exact wordToStackRegBoundFfi conf perf _ _ _ _ _ _ bs frame conventions room plain
  | shareInst _ _ _ => exact wordToStackRegBoundShareInst conf perf _ _ _ bs frame conventions room plain
  | mustTerminate body =>
      exact wordToStackRegBoundMustTerminate conf perf body bs frame conventions room plain
        (fun bs frame conventions room plain => wordToStackRegBound conf perf body bs frame conventions room plain)
  | loop liveIn body liveOut =>
      exact wordToStackRegBoundLoop conf perf liveIn liveOut body bs frame conventions room plain
        (fun bs frame conventions room plain => wordToStackRegBound conf perf body bs frame conventions room plain)
  | seq first second =>
      exact wordToStackRegBoundSeq conf perf first second bs frame conventions room plain
        (fun bs frame conventions room plain => wordToStackRegBound conf perf first bs frame conventions room plain)
        (fun bs frame conventions room plain => wordToStackRegBound conf perf second bs frame conventions room plain)
  | ite cmp reg ri first second =>
      exact wordToStackRegBoundIf conf perf cmp reg ri first second bs frame conventions room plain
        (fun bs frame conventions room plain => wordToStackRegBound conf perf first bs frame conventions room plain)
        (fun bs frame conventions room plain => wordToStackRegBound conf perf second bs frame conventions room plain)
  | call returns dest args handler =>
      cases returns with
      | none => exact wordToStackRegBoundCallTail conf perf dest args handler bs frame conventions room plain
      | some record =>
          match hRet : record with
          | (values,live,retCode,l1,l2) =>
              cases handler with
              | none =>
                  exact wordToStackRegBoundCallReturn conf perf values live retCode l1 l2
                    dest args bs frame conventions room plain
                    (fun bs frame conventions room plain => wordToStackRegBound conf perf retCode bs frame conventions room plain)
              | some record =>
                  match hHandle : record with
                  | (handleValue,handleCode,h1,h2) =>
                      exact wordToStackRegBoundCallHandler conf perf values live retCode handleCode
                        l1 l2 handleValue h1 h2 dest args bs frame conventions room plain
                        (fun bs frame conventions room plain => wordToStackRegBound conf perf retCode bs frame conventions room plain)
                        (fun bs frame conventions room plain => wordToStackRegBound conf perf handleCode bs frame conventions room plain)
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.WordToStackProofs.RegisterBoundCompiler
