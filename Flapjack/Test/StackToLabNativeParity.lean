import Flapjack.Compiler.Backend.StackToLab.Native
namespace Flapjack.Test.StackToLabNativeParity

open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
example : flattenHOL true (.seq .tick .skip : HolProg 64) 7 2 [] [] =
    (.append (.append (.list [.asm (.asmi (.inst .skip)) [] 0])
      (.list [.label 7 1 0])) (.list []), false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.loop (.break 0) : HolProg 64) 7 2 [] [] =
    (.append (.append (.list [.label 7 2 0])
      (.list [.labAsm (.jump (.lab 7 3)) 0 [] 0]))
      (.list [.labAsm (.jump (.lab 7 2)) 0 [] 0, .label 7 3 0]), false, 4) := by
  simp [flattenHOL, findLabHOL]
example : (progToSectionHOL (7, (.seq .tick .skip : HolProg 64))).lines =
    [.asm (.asmi (.inst .skip)) [] 0, .label 7 1 0, .label 7 2 0] := by
  simp [progToSectionHOL, flattenHOL, isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux]

-- Original complete output native_tick.
example : flattenHOL false (.tick : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.inst .skip)) [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_inst.
example : flattenHOL false (.inst .skip : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.inst .skip)) [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_halt.
example : flattenHOL false (.halt 99 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm .halt 0 [] 0], true, 2) := by
  simp [flattenHOL]

-- Original complete output native_raise.
example : flattenHOL false (.raise 999 : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.jumpReg 999)) [] 0], true, 2) := by
  simp [flattenHOL]

-- Original complete output native_return.
example : flattenHOL false (.ret 999 : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.jumpReg 999)) [] 0], true, 2) := by
  simp [flattenHOL]

-- Original complete output native_break_missing.
example : flattenHOL false (.break 100 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.jump (.lab 7 0)) 0 [] 0], true, 2) := by
  simp [flattenHOL, findLabHOL]

-- Original complete output native_continue_missing.
example : flattenHOL false (.continue 100 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.jump (.lab 7 0)) 0 [] 0], true, 2) := by
  simp [flattenHOL, findLabHOL]

-- Original complete output native_rawcall.
example : flattenHOL false (.rawCall 999 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.jump (.lab 999 1)) 0 [] 0], true, 2) := by
  simp [flattenHOL]

-- Original complete output native_tailcall_label.
example : flattenHOL false (.call none (.inl 999) none : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.jump (.lab 999 0)) 0 [] 0], true, 2) := by
  simp [flattenHOL, compileJumpHOL]

-- Original complete output native_tailcall_register.
example : flattenHOL false (.call none (.inr 999) (some (.tick,8,9)) : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.jumpReg 999)) [] 0], true, 2) := by
  simp [flattenHOL, compileJumpHOL]

-- Original complete output native_lower.
example : flattenHOL false (.jumpLower 3 4 999 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.jumpCmp .lower 3 (.reg 4) (.lab 999 0)) 0 [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_location.
example : flattenHOL false (.locValue 3 999 1000 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.locValue 3 (.lab 999 1000)) 0 [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_install.
example : flattenHOL false (.install 1 2 3 4 5 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.locValue 5 (.lab 7 2)) 0 [] 0, .labAsm .install 0 [] 0, .label 7 2 0], false, 3) := by
  simp [flattenHOL]

-- Original complete output native_shared.
example : flattenHOL false (.shMemOp .load 3 (.addr 4 0) : HolProg 64) 7 2 [] [] =
    (.list [.asm (.shareMem .load 3 (.addr 4 0)) [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_buffer.
example : flattenHOL false (.codeBufferWrite 3 4 : HolProg 64) 7 2 [] [] =
    (.list [.asm (.cbw 3 4) [] 0], false, 2) := by
  simp [flattenHOL]

-- Original complete output native_fallback.
example : flattenHOL false (.dataBufferWrite 3 4 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]

-- Complete original native_if_left_skip_tree.
example : flattenHOL false (.ite .less 3 (.reg 4) (.skip) (.tick) : HolProg 64) 7 2 [] [] =
    (.append (.append (.list [.labAsm (.jumpCmp .less 3 (.reg 4) (.lab 7 2)) 0 [] 0]) (.list [.asm (.asmi (.inst .skip)) [] 0])) (.list [.label 7 2 0]), false, 3) := by
  simp [flattenHOL, stackIsSkip]

-- Complete original native_if_right_skip_tree.
example : flattenHOL false (.ite .less 3 (.reg 4) (.tick) (.skip) : HolProg 64) 7 2 [] [] =
    (.append (.append (.list [.labAsm (.jumpCmp .notLess 3 (.reg 4) (.lab 7 2)) 0 [] 0]) (.list [.asm (.asmi (.inst .skip)) [] 0])) (.list [.label 7 2 0]), false, 3) := by
  simp [flattenHOL, stackIsSkip, negateHOL]

-- Complete original native_if_left_noreturn_tree.
example : flattenHOL false (.ite .less 3 (.reg 4) (.halt 5) (.tick) : HolProg 64) 7 2 [] [] =
    (.append (.append (.append (.list [.labAsm (.jumpCmp .notLess 3 (.reg 4) (.lab 7 2)) 0 [] 0]) (.list [.labAsm .halt 0 [] 0])) (.list [.label 7 2 0])) (.list [.asm (.asmi (.inst .skip)) [] 0]), false, 3) := by
  simp [flattenHOL, stackIsSkip, negateHOL]

-- Complete original native_if_right_noreturn_tree.
example : flattenHOL false (.ite .less 3 (.reg 4) (.tick) (.halt 5) : HolProg 64) 7 2 [] [] =
    (.append (.append (.append (.list [.labAsm (.jumpCmp .less 3 (.reg 4) (.lab 7 2)) 0 [] 0]) (.list [.labAsm .halt 0 [] 0])) (.list [.label 7 2 0])) (.list [.asm (.asmi (.inst .skip)) [] 0]), false, 3) := by
  simp [flattenHOL, stackIsSkip]

-- Complete original native_if_fallthrough_tree.
example : flattenHOL false (.ite .less 3 (.reg 4) (.tick) (.tick) : HolProg 64) 7 2 [] [] =
    (.append (.append (.append (.append (.list [.labAsm (.jumpCmp .less 3 (.reg 4) (.lab 7 2)) 0 [] 0]) (.list [.asm (.asmi (.inst .skip)) [] 0])) (.list [.labAsm (.jump (.lab 7 3)) 0 [] 0, .label 7 2 0])) (.list [.asm (.asmi (.inst .skip)) [] 0])) (.list [.label 7 3 0]), false, 4) := by
  simp [flattenHOL, stackIsSkip]

-- Complete original native_call_handler_tree, including inner association.
example : flattenHOL false (.call (some (.tick,3,8,9)) (.inl 4)
    (some (.tick,10,11)) : HolProg 64) 7 2 [] [] =
    (.append
      (.append (.list [.labAsm (.locValue 3 (.lab 8 9)) 0 [] 0,
        .labAsm (.jump (.lab 4 0)) 0 [] 0, .label 8 9 0])
        (.list [.asm (.asmi (.inst .skip)) [] 0]))
      (.append (.append (.list [.labAsm (.jump (.lab 7 2)) 0 [] 0,
        .label 10 11 0]) (.list [.asm (.asmi (.inst .skip)) [] 0]))
        (.list [.label 7 2 0])), false, 3) := by
  simp [flattenHOL, compileJumpHOL]

-- The FFI bytes are passed through unchanged; no String codec is involved.
example {width : Nat} [NeZero width]
    (name : Flapjack.Basis.Pure.MlString.MlString) :
    flattenHOL false (.ffi name 1 2 3 4 5 : HolProg width) 7 2 [] [] =
      (.list [.labAsm (.locValue 5 (.lab 7 2)) 0 [] 0,
        .labAsm (.callFFI name) 0 [] 0, .label 7 2 0], false, 3) := by
  simp [flattenHOL]

example : flattenHOL false (.inst (.const 999 1) : HolProg 1) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.const 999 1))) [] 0], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.inst (.const 999 1208925819614629174706175) : HolProg 80) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.const 999 1208925819614629174706175))) [] 0], false, 2) := by
  simp [flattenHOL]

-- Every native constructor omitted by the original quotation hits its wildcard.
example : flattenHOL false (.skip : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.get 1 .globals : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.set .globals 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.opCurrHeap .add 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.alloc 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.storeConsts 1 2 none : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackAlloc 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackFree 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackStore 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackStoreAny 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackLoad 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackLoadAny 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackGetSize 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.stackSetSize 1 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.bitmapLoad 1 2 : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL]

-- The both-Skip If branch discards both recursively empty outputs.
example : flattenHOL false (.ite .less 3 (.reg 4) .skip .skip : HolProg 64) 7 2 [] [] =
    (.list [], false, 2) := by
  simp [flattenHOL, stackIsSkip]
-- Returned Call without a handler emits exactly the prefix and return body.
example : flattenHOL false (.call (some (.tick,3,8,9)) (.inr 4) none : HolProg 64) 7 2 [] [] =
    (.append (.list [.labAsm (.locValue 3 (.lab 8 9)) 0 [] 0,
      .asm (.asmi (.jumpReg 4)) [] 0, .label 8 9 0])
      (.list [.asm (.asmi (.inst .skip)) [] 0]), false, 2) := by
  simp [flattenHOL, compileJumpHOL]

end Flapjack.Test.StackToLabNativeParity
