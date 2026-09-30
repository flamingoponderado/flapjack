import Flapjack.Compiler.Backend.StackProps.AllocArg
namespace Flapjack.Test.StackPropsAllocArg
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang
-- Original HOL one=T
example : allocArg (.alloc 1 : HolProg 8) := by simp [allocArg]
-- Original HOL zero=F
example : ¬ allocArg (.alloc 0 : HolProg 8) := by simp [allocArg]
-- Original HOL two=F
example : ¬ allocArg (.alloc 2 : HolProg 8) := by simp [allocArg]
-- Original HOL seq_good=T
example : allocArg (.seq (.alloc 1) .skip : HolProg 8) := by simp [allocArg]
-- Original HOL seq_bad=F
example : ¬ allocArg (.seq .skip (.alloc 2) : HolProg 8) := by simp [allocArg]
-- Original HOL if_good=T
example : allocArg (.ite .equal 99 (.reg 99) .skip (.alloc 1) : HolProg 8) := by simp [allocArg]
-- Original HOL if_bad=F
example : ¬ allocArg (.ite .equal 0 (.reg 0) (.alloc 0) .skip : HolProg 8) := by simp [allocArg]
-- Original HOL loop_good=T
example : allocArg (.loop (.alloc 1) : HolProg 8) := by simp [allocArg]
-- Original HOL loop_bad=F
example : ¬ allocArg (.loop (.alloc 2) : HolProg 8) := by simp [allocArg]
-- Original HOL call_none=T
example : allocArg (.call none (.inr 99) none : HolProg 8) := by simp [allocArg]
-- Original HOL call_none_handler_bad=F
example : ¬ allocArg (.call none (.inr 99) (some (.alloc 2,3,4)) : HolProg 8) := by simp [allocArg]
-- Original HOL call_return_bad=F
example : ¬ allocArg (.call (some (.alloc 0,99,1,2)) (.inr 99) none : HolProg 8) := by simp [allocArg]
-- Original HOL call_handler_bad=F
example : ¬ allocArg (.call (some (.skip,99,1,2)) (.inr 99) (some (.alloc 2,3,4)) : HolProg 8) := by simp [allocArg]
-- Original HOL call_good=T
example : allocArg (.call (some (.alloc 1,99,1,2)) (.inr 99) (some (.alloc 1,3,4)) : HolProg 8) := by simp [allocArg]
-- Original HOL inst_default=T
example : allocArg (.inst (.const 99 0) : HolProg 8) := by simp [allocArg]
end Flapjack.Test.StackPropsAllocArg
