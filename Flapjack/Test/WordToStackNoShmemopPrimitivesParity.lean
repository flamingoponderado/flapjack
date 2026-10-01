import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrimitives
namespace Flapjack.Test.WordToStackNoShmemopPrimitivesParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- cp_skip_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .skip;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_assign_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .assign 999 (.op .add [.var 999,.const 9]);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_store_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .store (.load (.var 999)) 777;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_raise_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .raise 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_break_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .break 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_continue_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .continue 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_tick_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .tick;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_skip_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .skip;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_assign_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .assign 999 (.op .add [.var 999,.const 9]);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_store_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .store (.load (.var 999)) 777;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_raise_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .raise 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_break_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .break 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_continue_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .continue 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_tick_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .tick;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_skip_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .skip;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_assign_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .assign 999 (.op .add [.var 999,.const 9]);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_store_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .store (.load (.var 999)) 777;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_raise_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .raise 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_break_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .break 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_continue_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .continue 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_tick_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .tick;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_skip_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .skip;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_assign_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .assign 999 (.op .add [.var 999,.const 9]);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_store_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .store (.load (.var 999)) 777;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_raise_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .raise 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_break_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .break 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_continue_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .continue 999;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_tick_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .tick;
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (true, true) := by
  simp only [compNative]
  rfl

-- cp_load_valid
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .shareInst .load 999 (.var 3);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- cp_load_invalid
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .shareInst .load 999 (.const 9);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

-- cp_store_valid
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .shareInst .store 999 (.var 3);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1) =
      (false, false) := by
  simp only [compNative]
  rfl

-- cp_store_invalid
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .shareInst .store 999 (.const 9);
    (noShareInstSubprogsHOL p,
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1) =
      (false, true) := by
  simp only [compNative]
  rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.skip) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.skip) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopSkip conf perf bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : Nat) (value : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.assign name value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.assign name value) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopAssign conf perf name value bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (address : WordLangExpHOL (BitVec width)) (value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.store address value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.store address value) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopStore conf perf address value bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.raise value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.raise value) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopRaise conf perf value bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.break label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.break label) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopBreak conf perf label bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.continue label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.continue label) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopContinue conf perf label bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL ((.tick) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.tick) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopTick conf perf bs frame output residual _guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (operator : WordMemOp) (name : Nat) (address : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.shareInst operator name address) : WordLangProgHOL (BitVec width)) = true)
    (_compiled : compNative conf perf (.shareInst operator name address) bs frame = (output,residual)) :
    noShmemop output = true :=
  compNoShmemopShareInst conf perf operator name address bs frame output residual guard _compiled

end Flapjack.Test.WordToStackNoShmemopPrimitivesParity
