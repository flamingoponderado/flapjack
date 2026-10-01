import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopRecursive

namespace Flapjack.Test.WordToStackNoShmemopRecursiveParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- rc_must_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .mustTerminate (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6]));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_loop_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .loop (.bn .ln .ln) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_seq_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .seq (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_reg_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ite .equal 999 (.reg 3) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_must_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .mustTerminate (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6]));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_loop_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .loop (.bn .ln .ln) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_seq_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .seq (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_reg_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ite .equal 999 (.reg 3) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_must_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6]));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_loop_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .loop (.bn .ln .ln) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_seq_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_reg_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.reg 3) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_must_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .mustTerminate (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6]));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_loop_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .loop (.bn .ln .ln) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_seq_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .seq (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_reg_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ite .equal 999 (.reg 3) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ite .less 999 (.imm 9) (.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.return 999 [2,4,6])) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- rc_must_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.shareInst .load 999 (.var 3));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_must_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.shareInst .load 999 (.const 9));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_must_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .mustTerminate (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12)));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_loop_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .loop (.bn .ln .ln) (.shareInst .load 999 (.var 3)) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_loop_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .loop (.bn .ln .ln) (.shareInst .load 999 (.const 9)) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_loop_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .loop (.bn .ln .ln) (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12))) (.bs .ln () .ln);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_seq_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.shareInst .load 999 (.var 3)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_seq_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.shareInst .load 999 (.const 9)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_seq_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .seq (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12))) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_reg_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.reg 3) (.shareInst .load 999 (.var 3)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_reg_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.reg 3) (.shareInst .load 999 (.const 9)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_reg_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .equal 999 (.reg 3) (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12))) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative (conf) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.shareInst .load 999 (.var 3)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.shareInst .load 999 (.const 9)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_imm_yes_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12))) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => true }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_shared
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.shareInst .load 999 (.var 3)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- rc_imm_no_invalid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.shareInst .load 999 (.const 9)) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- rc_imm_no_ignored_handler
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ite .less 999 (.imm 9) (.call none (some 9) [] (some (777,.shareInst .load 999 (.var 3),11,12))) (.seq (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.locValue 999 777));
    (noShareInstSubprogsHOL p,
      noShmemop (compNative ({ conf with validImm := fun _ _ => false }) true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- Full original case application, including its genuine subprogram IH.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.mustTerminate body) = true)
    (compiled : compNative conf perf (.mustTerminate body) bs frame = (output, residual))
    (ih : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL body = true →
      compNative conf perf body subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true :=
  compNoShmemopMustTerminate conf perf body bs frame output residual guard compiled ih

-- Full original case application, including its genuine subprogram IH.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (liveIn liveOut : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.loop liveIn body liveOut) = true)
    (compiled : compNative conf perf (.loop liveIn body liveOut) bs frame = (output, residual))
    (ih : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL body = true →
      compNative conf perf body subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true :=
  compNoShmemopLoop conf perf liveIn liveOut body bs frame output residual guard compiled ih

-- Full original case application, including its genuine subprogram IH.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.seq first second) = true)
    (compiled : compNative conf perf (.seq first second) bs frame = (output, residual))
    (ihFirst : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL first = true →
      compNative conf perf first subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true)
    (ihSecond : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL second = true →
      compNative conf perf second subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true :=
  compNoShmemopSeq conf perf first second bs frame output residual guard compiled ihFirst ihSecond

-- Full original case application, including its genuine subprogram IH.
example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (cmp : Cmp) (reg : Nat) (ri : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.ite cmp reg ri first second) = true)
    (compiled : compNative conf perf (.ite cmp reg ri first second) bs frame = (output, residual))
    (ihFirst : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL first = true →
      compNative conf perf first subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true)
    (ihSecond : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL second = true →
      compNative conf perf second subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true :=
  compNoShmemopIf conf perf cmp reg ri first second bs frame output residual guard compiled ihFirst ihSecond

end Flapjack.Test.WordToStackNoShmemopRecursiveParity
