import Flapjack.Compiler.Backend.StackProps.RemoveNames
namespace Flapjack.Test.StackPropsRemoveNames
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
-- Original HOL get_last=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 5 .currHeap) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL get_bound=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.get 6 .currHeap) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL set=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.set .currHeap 1) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL store_ignored_second=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 1 99) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL store_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStore 6 1) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL load_ignored_second=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 1 99) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL load_first_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoad 6 1) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL get_size=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackGetSize 1) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL set_size_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackSetSize 6) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL heap=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.opCurrHeap .add 1 2) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL store_any_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackStoreAny 1 6) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL load_any=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.stackLoadAny 1 2) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL bitmap_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.bitmapLoad 6 1) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL consts=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.storeConsts 1 2 (some 99)) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL seq_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.seq (.get 1 .currHeap) (.get 6 .currHeap)) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL if_ignored_condition=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.ite .equal 99 (.reg 99) .skip .skip) : HolProg 8) := by
  simp [stackAsmRemove]
-- Original HOL loop_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.loop (.get 6 .currHeap)) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL call_none_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call none (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by
  simp [stackAsmRemove]
-- Original HOL call_body_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 6 .currHeap,99,1,2)) (.inr 99) none) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL call_handler_bad=F
example (c : AsmConfigExact 8) : ¬ stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.skip,99,1,2)) (.inr 99) (some (.get 6 .currHeap,3,4))) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL call_both_good=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.call (some (.get 1 .currHeap,99,1,2)) (.inr 99) (some (.get 2 .currHeap,3,4))) : HolProg 8) := by
  simp [stackAsmRemove, regName]
-- Original HOL inst_ignored=T
example (c : AsmConfigExact 8) : stackAsmRemove {c with regCount := 8, avoidRegs := [0,1]} ((.inst (.const 99 0)) : HolProg 8) := by
  simp [stackAsmRemove]
end Flapjack.Test.StackPropsRemoveNames
