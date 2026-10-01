import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopFlatEffects
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrimitives

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original compiler preservation for every source constructor. The
original source guard and actual compiler equality are the only hypotheses;
constructor induction hypotheses are discharged by terminating recursion. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL program = true)
    (compiled : compNative conf perf program bs frame = (output,residual)) :
    noShmemop output = true := by
  cases program with
  | skip =>
      exact compNoShmemopSkip conf perf bs frame output residual guard compiled
  | move priority moves =>
      exact compNoShmemopMove conf perf priority moves bs frame output residual guard compiled
  | inst instruction =>
      exact compNoShmemopInst conf perf instruction bs frame output residual guard compiled
  | assign name value =>
      exact compNoShmemopAssign conf perf name value bs frame output residual guard compiled
  | get destination name =>
      exact compNoShmemopGet conf perf destination name bs frame output residual guard compiled
  | set name value =>
      exact compNoShmemopSet conf perf name value bs frame output residual guard compiled
  | store address value =>
      exact compNoShmemopStore conf perf address value bs frame output residual guard compiled
  | alloc destination live =>
      exact compNoShmemopAlloc conf perf destination live bs frame output residual guard compiled
  | storeConsts source bitmap codeLength dataLength constants =>
      exact compNoShmemopStoreConsts conf perf source bitmap codeLength dataLength constants bs frame output residual guard compiled
  | raise value =>
      exact compNoShmemopRaise conf perf value bs frame output residual guard compiled
  | «return» label values =>
      exact compNoShmemopReturn conf perf label values bs frame output residual guard compiled
  | «break» label =>
      exact compNoShmemopBreak conf perf label bs frame output residual guard compiled
  | «continue» label =>
      exact compNoShmemopContinue conf perf label bs frame output residual guard compiled
  | tick =>
      exact compNoShmemopTick conf perf bs frame output residual guard compiled
  | opCurrHeap operator destination source =>
      exact compNoShmemopOpCurrHeap conf perf operator destination source bs frame output residual guard compiled
  | locValue destination source =>
      exact compNoShmemopLocValue conf perf destination source bs frame output residual guard compiled
  | install codeBuffer codeLength dataBuffer dataLength live =>
      exact compNoShmemopInstall conf perf codeBuffer codeLength dataBuffer dataLength live bs frame output residual guard compiled
  | codeBufferWrite address value =>
      exact compNoShmemopCodeBufferWrite conf perf address value bs frame output residual guard compiled
  | dataBufferWrite address value =>
      exact compNoShmemopDataBufferWrite conf perf address value bs frame output residual guard compiled
  | ffi name configuration configurationLength array arrayLength live =>
      exact compNoShmemopFFI conf perf name configuration configurationLength array arrayLength live bs frame output residual guard compiled
  | shareInst operator name address =>
      exact compNoShmemopShareInst conf perf operator name address bs frame output residual guard compiled
  | mustTerminate body =>
      exact compNoShmemopMustTerminate conf perf body bs frame output residual guard compiled
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf body subBs subFrame subOutput subResidual subGuard subCompiled)
  | loop liveIn body liveOut =>
      exact compNoShmemopLoop conf perf liveIn liveOut body bs frame output residual guard compiled
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf body subBs subFrame subOutput subResidual subGuard subCompiled)
  | seq first second =>
      exact compNoShmemopSeq conf perf first second bs frame output residual guard compiled
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf first subBs subFrame subOutput subResidual subGuard subCompiled)
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf second subBs subFrame subOutput subResidual subGuard subCompiled)
  | ite cmp reg ri first second =>
      exact compNoShmemopIf conf perf cmp reg ri first second bs frame output residual guard compiled
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf first subBs subFrame subOutput subResidual subGuard subCompiled)
        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
          compNoShmemop conf perf second subBs subFrame subOutput subResidual subGuard subCompiled)
  | call returns destination args handler =>
      cases returns with
      | none =>
          exact compNoShmemopTailCall conf perf destination args handler bs frame output residual guard compiled
      | some record =>
          match hRetRecord : record with
          | (values,live,retCode,label1,label2) =>
              cases handler with
              | none =>
                  exact compNoShmemopReturningCall conf perf values live retCode label1 label2
                    destination args bs frame output residual guard compiled
                    (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
                      compNoShmemop conf perf retCode subBs subFrame subOutput subResidual subGuard subCompiled)
              | some record =>
                  match hHandlerRecord : record with
                  | (handleValue,handleCode,handleLabel1,handleLabel2) =>
                      exact compNoShmemopHandledCall conf perf values live retCode label1 label2
                        destination args handleValue handleCode handleLabel1 handleLabel2
                        bs frame output residual guard compiled
                        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
                          compNoShmemop conf perf retCode subBs subFrame subOutput subResidual subGuard subCompiled)
                        (fun subBs subFrame subOutput subResidual subGuard subCompiled =>
                          compNoShmemop conf perf handleCode subBs subFrame subOutput subResidual subGuard subCompiled)

termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.Compiler.Backend.WordToStack.Native
