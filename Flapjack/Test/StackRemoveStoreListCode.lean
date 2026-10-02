import Flapjack.Compiler.Backend.StackRemove.StoreListCode

/-! Full original output observations captured by store_list_code_probeScript.sml.
Explicit native trees preserve terminal Skip, right-nested sequences, temporary
and address aliasing, arbitrary natural registers and narrow/wide word values. -/
namespace Flapjack.Test.StackRemoveStoreListCode
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- store_list_code_1_0
example : storeListCode (width := 1) 0 0 [] =
    .skip := by rfl

-- store_list_code_1_1
example : storeListCode (width := 1) 5 6 [.inl 17] =
    .seq (.seq (.inst (.const 6 17)) (.seq (.inst (.mem .store 6 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 0)))))) (.skip) := by rfl

-- store_list_code_1_2
example : storeListCode (width := 1) 5 6 [.inr 9] =
    .seq (.seq (.inst (.mem .store 9 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 0))))) (.skip) := by rfl

-- store_list_code_1_3
example : storeListCode (width := 1) 7 7 [.inl 0, .inr 7, .inl 1208925819614629174706193] =
    .seq (.seq (.inst (.const 7 0)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 0))))) (.seq (.seq (.inst (.const 7 1208925819614629174706193)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 0)))))) (.skip))) := by rfl

-- store_list_code_1_4
example : storeListCode (width := 1) 1180591620717411303427 1180591620717411303429 [.inr 1180591620717411303431, .inl 255] =
    .seq (.seq (.inst (.mem .store 1180591620717411303431 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 0))))) (.seq (.seq (.inst (.const 1180591620717411303429 255)) (.seq (.inst (.mem .store 1180591620717411303429 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 0)))))) (.skip)) := by rfl

-- store_list_code_1_5
example : storeListCode (width := 1) 31 0 [.inl 1, .inr 31, .inr 0, .inl 0] =
    .seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 31 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 0))))) (.seq (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 0))))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 0)))))) (.skip)))) := by rfl

-- store_list_code_8_0
example : storeListCode (width := 8) 0 0 [] =
    .skip := by rfl

-- store_list_code_8_1
example : storeListCode (width := 8) 5 6 [.inl 17] =
    .seq (.seq (.inst (.const 6 17)) (.seq (.inst (.mem .store 6 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 1)))))) (.skip) := by rfl

-- store_list_code_8_2
example : storeListCode (width := 8) 5 6 [.inr 9] =
    .seq (.seq (.inst (.mem .store 9 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 1))))) (.skip) := by rfl

-- store_list_code_8_3
example : storeListCode (width := 8) 7 7 [.inl 0, .inr 7, .inl 1208925819614629174706193] =
    .seq (.seq (.inst (.const 7 0)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 1))))) (.seq (.seq (.inst (.const 7 1208925819614629174706193)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 1)))))) (.skip))) := by rfl

-- store_list_code_8_4
example : storeListCode (width := 8) 1180591620717411303427 1180591620717411303429 [.inr 1180591620717411303431, .inl 255] =
    .seq (.seq (.inst (.mem .store 1180591620717411303431 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 1))))) (.seq (.seq (.inst (.const 1180591620717411303429 255)) (.seq (.inst (.mem .store 1180591620717411303429 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 1)))))) (.skip)) := by rfl

-- store_list_code_8_5
example : storeListCode (width := 8) 31 0 [.inl 1, .inr 31, .inr 0, .inl 0] =
    .seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 31 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 1))))) (.seq (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 1))))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 1)))))) (.skip)))) := by rfl

-- store_list_code_64_0
example : storeListCode (width := 64) 0 0 [] =
    .skip := by rfl

-- store_list_code_64_1
example : storeListCode (width := 64) 5 6 [.inl 17] =
    .seq (.seq (.inst (.const 6 17)) (.seq (.inst (.mem .store 6 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 8)))))) (.skip) := by rfl

-- store_list_code_64_2
example : storeListCode (width := 64) 5 6 [.inr 9] =
    .seq (.seq (.inst (.mem .store 9 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 8))))) (.skip) := by rfl

-- store_list_code_64_3
example : storeListCode (width := 64) 7 7 [.inl 0, .inr 7, .inl 1208925819614629174706193] =
    .seq (.seq (.inst (.const 7 0)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 8))))) (.seq (.seq (.inst (.const 7 1208925819614629174706193)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 8)))))) (.skip))) := by rfl

-- store_list_code_64_4
example : storeListCode (width := 64) 1180591620717411303427 1180591620717411303429 [.inr 1180591620717411303431, .inl 255] =
    .seq (.seq (.inst (.mem .store 1180591620717411303431 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 8))))) (.seq (.seq (.inst (.const 1180591620717411303429 255)) (.seq (.inst (.mem .store 1180591620717411303429 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 8)))))) (.skip)) := by rfl

-- store_list_code_64_5
example : storeListCode (width := 64) 31 0 [.inl 1, .inr 31, .inr 0, .inl 0] =
    .seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 31 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 8))))) (.seq (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 8))))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 8)))))) (.skip)))) := by rfl

-- store_list_code_80_0
example : storeListCode (width := 80) 0 0 [] =
    .skip := by rfl

-- store_list_code_80_1
example : storeListCode (width := 80) 5 6 [.inl 17] =
    .seq (.seq (.inst (.const 6 17)) (.seq (.inst (.mem .store 6 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 10)))))) (.skip) := by rfl

-- store_list_code_80_2
example : storeListCode (width := 80) 5 6 [.inr 9] =
    .seq (.seq (.inst (.mem .store 9 (.addr 5 0))) (.inst (.arith (.binop .add 5 5 (.imm 10))))) (.skip) := by rfl

-- store_list_code_80_3
example : storeListCode (width := 80) 7 7 [.inl 0, .inr 7, .inl 1208925819614629174706193] =
    .seq (.seq (.inst (.const 7 0)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 10))))) (.seq (.seq (.inst (.const 7 1208925819614629174706193)) (.seq (.inst (.mem .store 7 (.addr 7 0))) (.inst (.arith (.binop .add 7 7 (.imm 10)))))) (.skip))) := by rfl

-- store_list_code_80_4
example : storeListCode (width := 80) 1180591620717411303427 1180591620717411303429 [.inr 1180591620717411303431, .inl 255] =
    .seq (.seq (.inst (.mem .store 1180591620717411303431 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 10))))) (.seq (.seq (.inst (.const 1180591620717411303429 255)) (.seq (.inst (.mem .store 1180591620717411303429 (.addr 1180591620717411303427 0))) (.inst (.arith (.binop .add 1180591620717411303427 1180591620717411303427 (.imm 10)))))) (.skip)) := by rfl

-- store_list_code_80_5
example : storeListCode (width := 80) 31 0 [.inl 1, .inr 31, .inr 0, .inl 0] =
    .seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 31 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 10))))) (.seq (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 10))))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 31 0))) (.inst (.arith (.binop .add 31 31 (.imm 10)))))) (.skip)))) := by rfl

end Flapjack.Test.StackRemoveStoreListCode
