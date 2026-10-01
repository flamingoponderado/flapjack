import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
namespace Flapjack.Test.WordToStackNoShmemopTailCallParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- tc_direct0_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_directmany_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirect0_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectsmall_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectlarge_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_direct0_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call none (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_directmany_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call none (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirect0_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call none none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectsmall_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call none none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectlarge_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .call none none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_direct0_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_directmany_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirect0_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectsmall_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectlarge_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_direct0_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call none (some 777) [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_directmany_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call none (some 777) [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirect0_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call none none [] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectsmall_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call none none [0] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_indirectlarge_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .call none none [2,4,999] none;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_ignored_safe
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [999] (some (99,.return 999 [2,4],7,9));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- tc_ignored_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [999] (some (99,.shareInst .load 0 (.var 3),7,9));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (destination : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL (.call none destination args handler) = true)
    (compiled : compNative conf perf (.call none destination args handler) bs frame =
      (output, residual)) :
    noShmemop output = true :=
  compNoShmemopTailCall conf perf destination args handler bs frame output residual _guard compiled

end Flapjack.Test.WordToStackNoShmemopTailCallParity
