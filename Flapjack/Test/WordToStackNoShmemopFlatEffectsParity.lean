import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopFlatEffects

namespace Flapjack.Test.WordToStackNoShmemopFlatEffectsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- fe_move_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .move 9 [(2,4),(4,2),(6,2)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor
  · rfl
  · simp only [wMoveNative, wMoveAuxNoShmemop]

-- fe_return_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .return 999 [2,4,6];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_heap_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .opCurrHeap .add 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .set .currHeap (.var 999);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_get_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .get 999 .currHeap;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_alloc_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .alloc 999 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_consts_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .storeConsts 999 3 5 7 [(true,4),(false,7)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_loc_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .locValue 999 777;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_install_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .install 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_code_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .codeBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_data_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .dataBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_ffi_1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .ffi (.implode [102,102,105]) 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (0,0,0)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_move_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .move 9 [(2,4),(4,2),(6,2)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor
  · rfl
  · simp only [wMoveNative, wMoveAuxNoShmemop]

-- fe_return_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .return 999 [2,4,6];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_heap_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .opCurrHeap .add 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .set .currHeap (.var 999);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_get_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .get 999 .currHeap;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_alloc_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .alloc 999 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_consts_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .storeConsts 999 3 5 7 [(true,4),(false,7)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_loc_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .locValue 999 777;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_install_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .install 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_code_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .codeBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_data_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .dataBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_ffi_32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .ffi (.implode [102,102,105]) 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_move_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .move 9 [(2,4),(4,2),(6,2)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor
  · rfl
  · simp only [wMoveNative, wMoveAuxNoShmemop]

-- fe_return_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .return 999 [2,4,6];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_heap_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .opCurrHeap .add 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .currHeap (.var 999);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_get_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .get 999 .currHeap;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_alloc_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .alloc 999 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_consts_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .storeConsts 999 3 5 7 [(true,4),(false,7)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_loc_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .locValue 999 777;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_install_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .install 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_code_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .codeBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_data_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .dataBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_ffi_64
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .ffi (.implode [102,102,105]) 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p (.append (.list [4]) (.list [7]),17) (4,1,2)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_move_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .move 9 [(2,4),(4,2),(6,2)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor
  · rfl
  · simp only [wMoveNative, wMoveAuxNoShmemop]

-- fe_return_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .return 999 [2,4,6];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_heap_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .opCurrHeap .add 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .set .currHeap (.var 999);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_get_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .get 999 .currHeap;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_alloc_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .alloc 999 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_consts_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .storeConsts 999 3 5 7 [(true,4),(false,7)];
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_loc_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .locValue 999 777;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_install_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .install 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_code_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .codeBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_data_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .dataBufferWrite 999 3;
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_ffi_80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .ffi (.implode [102,102,105]) 999 3 5 7 (.bs .ln () .ln, .bn .ln .ln);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (9,999,3)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_bitmap
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .bitmapBase (.var 999);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_const
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .currHeap (.const 9);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_lookup
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set (.temp 31) (.lookup .currHeap);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_load
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .currHeap (.load (.var 999));
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_op
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .currHeap (.op .add [.var 999,.const 9]);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

-- fe_set_shift
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .set .currHeap (.shift .lsl (.var 999) (.const 9));
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p (.append (.list [4]) (.list [7]),17) (2,7,9)).1 = true := by
  simp only [compNative]
  constructor <;> rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (priority : Nat) (moves : List (Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.move priority moves) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.move priority moves) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopMove conf perf priority moves bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (label : Nat) (values : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.return label values) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.return label values) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopReturn conf perf label values bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (op : BinOp) (dst src : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.opCurrHeap op dst src) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.opCurrHeap op dst src) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopOpCurrHeap conf perf op dst src bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : WordStoreHOL) (value : WordLangExpHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.set name value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.set name value) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopSet conf perf name value bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst : Nat) (name : WordStoreHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.get dst name) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.get dst name) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopGet conf perf dst name bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.alloc dst live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.alloc dst live) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopAlloc conf perf dst live bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (src bitmap codeLength dataLength : Nat)
    (constants : List (Bool × BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.storeConsts src bitmap codeLength dataLength constants) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.storeConsts src bitmap codeLength dataLength constants) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopStoreConsts conf perf src bitmap codeLength dataLength constants bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (dst label : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.locValue dst label) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.locValue dst label) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopLocValue conf perf dst label bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (codeBuffer codeLength dataBuffer dataLength : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.install codeBuffer codeLength dataBuffer dataLength live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.install codeBuffer codeLength dataBuffer dataLength live) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopInstall conf perf codeBuffer codeLength dataBuffer dataLength live bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (addr value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.codeBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.codeBufferWrite addr value) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopCodeBufferWrite conf perf addr value bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (addr value : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.dataBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.dataBufferWrite addr value) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopDataBufferWrite conf perf addr value bs frame output residual guard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (name : Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL ((.ffi name configuration configurationLength array arrayLength live) : WordLangProgHOL (BitVec width)) = true)
    (compiled : compNative conf perf (.ffi name configuration configurationLength array arrayLength live) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopFFI conf perf name configuration configurationLength array arrayLength live bs frame output residual guard compiled

end Flapjack.Test.WordToStackNoShmemopFlatEffectsParity
