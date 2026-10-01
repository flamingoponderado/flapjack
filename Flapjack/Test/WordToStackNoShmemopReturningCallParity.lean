import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
namespace Flapjack.Test.WordToStackNoShmemopReturningCallParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- cr_direct0_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_directmany_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirect0_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectsmall_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectlarge_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_direct0_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_directmany_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirect0_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectsmall_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectlarge_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_direct0_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_directmany_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirect0_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectsmall_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectlarge_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_direct0_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_directmany_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirect0_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectsmall_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call (some ([],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_indirectlarge_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cr_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.shareInst .load 0 (.var 3)),7,9)) none [999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- cr_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.shareInst .load 0 (.const 9)),7,9)) none [999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (values : List Nat) (live : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (label1 label2 : Nat)
    (destination : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL
      (.call (some (values,live,retCode,label1,label2)) destination args none) = true)
    (compiled : compNative conf perf
      (.call (some (values,live,retCode,label1,label2)) destination args none) bs frame =
      (output, residual))
    (ihReturn : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL retCode = true →
      compNative conf perf retCode subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true :=
  compNoShmemopReturningCall conf perf values live retCode label1 label2 destination args bs frame output residual guard compiled ihReturn

end Flapjack.Test.WordToStackNoShmemopReturningCallParity
