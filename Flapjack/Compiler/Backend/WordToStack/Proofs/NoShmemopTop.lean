import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrograms
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original top-level no-shared-memory theorem, with HOL fixed false
performance flag, full compilation quadruple, and both injected stubs. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compileNoShmemop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (frameConfig : Config)
    (frames : List Nat) (outputs : List (Nat × HolProg width))
    (compiled : compileNative conf false programs = (bitmaps,frameConfig,frames,outputs))
    (guard : (programs.all fun row => noShareInstSubprogsHOL row.2.2) = true) :
    (outputs.all fun row => noShmemop row.2) = true := by
  have bodiesSafe := compileWordToStackNoShareInst conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) programs (.list [4],1)
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).1
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).2.1
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).2.2 guard rfl
  have result := congrArg (fun row => row.2.2.2) compiled
  simp only [compileNative, Bool.false_eq_true, ↓reduceIte] at result
  rw [← result]
  simpa only [List.all_cons, raiseStubNative, storeConstsStubNative,
    noShmemop, Bool.false_eq_true, ↓reduceIte, Bool.true_and] using bodiesSafe
end Flapjack.Compiler.Backend.WordToStack.Native
