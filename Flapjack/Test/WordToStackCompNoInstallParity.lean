import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallCompiler
set_option maxRecDepth 16384
namespace Flapjack.Test.WordToStackCompNoInstallParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
-- ci_skip_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .skip;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_move_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .move 17 [];
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  simp only [wMoveNative, wMoveAuxNoInstall]
  rfl

-- ci_inst_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpMovToReg 999 777 11));
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_assign_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .assign 999 (.const 7);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_get_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .get 999 .currHeap;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_set_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .handler (.var 999);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_store_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .store (.var 3) 999;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_alloc_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .alloc 999 (.bs .ln () .ln,.bn .ln .ln);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_store_consts_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .storeConsts 0 1 2 3 [(true,7),(false,8)];
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_raise_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .raise 999;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_return_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .return 999 [2,4,6];
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_break_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .break 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_continue_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .continue 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_tick_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .tick;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_heap_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .opCurrHeap .add 999 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_loc_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .locValue 999 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_install_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .install 0 1 2 3 (.ln,.ln);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false,false) := by
  simp only [compNative]
  rfl

-- ci_code_write_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .codeBufferWrite 999 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_data_write_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .dataBufferWrite 999 777;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_ffi_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_share_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .shareInst .load 999 (.var 3);
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_must_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate .tick;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_loop_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .loop .ln (.seq .tick .skip) .ln;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_seq_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.alloc 999 (.ln,.ln)) (.shareInst .store 999 (.var 3));
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_branch_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.reg 777) .tick .skip;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_call_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .call none none [2,4,999] none;
    (noInstallSubprogsHOL p,noInstall
      (compNative conf false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true,true) := by
  simp only [compNative]
  rfl

-- ci_nested_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_if_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noInstallSubprogsHOL p,
      noInstall (compNative ({conf with validImm := fun _ _ => false}) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_ignored_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_nested_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_if_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noInstallSubprogsHOL p,
      noInstall (compNative ({conf with validImm := fun _ _ => true}) false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_ignored_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_nested_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_if_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noInstallSubprogsHOL p,
      noInstall (compNative ({conf with validImm := fun _ _ => false}) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_ignored_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_nested_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .mustTerminate (.loop (.bn .ln .ln) (.seq (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none)) (.bs .ln () .ln));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_if_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ite .equal 999 (.imm 9) (.call (some ([2,4,6],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) none [2,4,999] (some (999,(.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777)),777,888))) (.call (some ([999],(.bs .ln () .ln,.bn .ln .ln),(.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])),7,9)) (some 777) [] none);
    (noInstallSubprogsHOL p,
      noInstall (compNative ({conf with validImm := fun _ _ => true}) false p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_ignored_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .seq (.assign 999 (.op .add [.var 999,.const 9])) (.mustTerminate (.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9))));
    (noInstallSubprogsHOL p,
      noInstall (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl


-- ci_ignored_install
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .call none none []
      (some (0,.install 0 1 2 3 (.ln,.ln),7,9));
    (noInstallSubprogsHOL p,noInstall (compNative conf false p (.list [],0) (0,0,0)).1) =
      (false,true) := by
  simp only [compNative]
  rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noInstallSubprogsHOL p = true)
    (compiled : compNative conf perf p bs frame = (output,residual))
    (plain : perf = false) : noInstall output = true :=
  compNoInstall conf perf p bs frame output residual guard compiled plain

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (guard : noInstallSubprogsHOL p = true) :
    noInstall (compNative conf false p bs frame).1 = true :=
  compNoInstall conf false p bs frame (compNative conf false p bs frame).1
    (compNative conf false p bs frame).2 guard rfl rfl
end Flapjack.Test.WordToStackCompNoInstallParity
