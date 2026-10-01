import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop
namespace Flapjack.Test.WordToStackCompNoShmemopParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- cs_nested_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_if_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({conf with validImm := fun _ _ => false}) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_ignored_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- cs_nested_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_if_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({conf with validImm := fun _ _ => true}) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_ignored_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- cs_nested_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_if_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({conf with validImm := fun _ _ => false}) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_ignored_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- cs_nested_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_if_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({conf with validImm := fun _ _ => true}) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cs_ignored_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- The complete original arbitrary-program theorem, with no public IH.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL program = true)
    (compiled : compNative conf perf program bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemop conf perf program bs frame output residual guard compiled

-- Actual compiler projections satisfy the original compilation equality.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (guard : noShareInstSubprogsHOL program = true) :
    noShmemop (compNative conf perf program bs frame).1 = true :=
  compNoShmemop conf perf program bs frame
    (compNative conf perf program bs frame).1
    (compNative conf perf program bs frame).2 guard rfl

end Flapjack.Test.WordToStackCompNoShmemopParity
