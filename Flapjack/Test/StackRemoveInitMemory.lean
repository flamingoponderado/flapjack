import Flapjack.Compiler.Backend.StackRemove.InitMemory
namespace Flapjack.Test.StackRemoveInitMemory
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
-- init_memory_1_0_0; original full-tree equality = T
example : initMemory (width := 1) 0 [] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.skip))))) := by rfl

-- init_memory_1_0_1; original full-tree equality = T
example : initMemory (width := 1) 0 [.inl 17] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 0)))))) (.skip)))))) := by rfl

-- init_memory_1_0_2; original full-tree equality = T
example : initMemory (width := 1) 0 [.inr 0] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 0))))) (.skip)))))) := by rfl

-- init_memory_1_0_3; original full-tree equality = T
example : initMemory (width := 1) 0 [.inl 0, .inr 0, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 0))))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 0)))))) (.skip)))))))) := by rfl

-- init_memory_1_1_0; original full-tree equality = T
example : initMemory (width := 1) 1 [] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.skip))))) := by rfl

-- init_memory_1_1_1; original full-tree equality = T
example : initMemory (width := 1) 1 [.inl 17] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 0)))))) (.skip)))))) := by rfl

-- init_memory_1_1_2; original full-tree equality = T
example : initMemory (width := 1) 1 [.inr 0] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 0))))) (.skip)))))) := by rfl

-- init_memory_1_1_3; original full-tree equality = T
example : initMemory (width := 1) 1 [.inl 0, .inr 1, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 1 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 0))))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 0)))))) (.skip)))))))) := by rfl

-- init_memory_1_23_0; original full-tree equality = T
example : initMemory (width := 1) 23 [] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.skip))))) := by rfl

-- init_memory_1_23_1; original full-tree equality = T
example : initMemory (width := 1) 23 [.inl 17] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 0)))))) (.skip)))))) := by rfl

-- init_memory_1_23_2; original full-tree equality = T
example : initMemory (width := 1) 23 [.inr 0] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 0))))) (.skip)))))) := by rfl

-- init_memory_1_23_3; original full-tree equality = T
example : initMemory (width := 1) 23 [.inl 0, .inr 23, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 23 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 0))))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 0)))))) (.skip)))))))) := by rfl

-- init_memory_1_1208925819614629174706185_0; original full-tree equality = T
example : initMemory (width := 1) 1208925819614629174706185 [] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.skip))))) := by rfl

-- init_memory_1_1208925819614629174706185_1; original full-tree equality = T
example : initMemory (width := 1) 1208925819614629174706185 [.inl 17] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 0)))))) (.skip)))))) := by rfl

-- init_memory_1_1208925819614629174706185_2; original full-tree equality = T
example : initMemory (width := 1) 1208925819614629174706185 [.inr 0] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 0))))) (.skip)))))) := by rfl

-- init_memory_1_1208925819614629174706185_3; original full-tree equality = T
example : initMemory (width := 1) 1208925819614629174706185 [.inl 0, .inr 1208925819614629174706185, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 0)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 0)))))) (.seq (.seq (.inst (.mem .store 1208925819614629174706185 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 0))))) (.seq (.seq (.inst (.const 0 1)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 0)))))) (.skip)))))))) := by rfl

-- init_memory_8_0_0; original full-tree equality = T
example : initMemory (width := 8) 0 [] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.skip))))) := by rfl

-- init_memory_8_0_1; original full-tree equality = T
example : initMemory (width := 8) 0 [.inl 17] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 1)))))) (.skip)))))) := by rfl

-- init_memory_8_0_2; original full-tree equality = T
example : initMemory (width := 8) 0 [.inr 0] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 1))))) (.skip)))))) := by rfl

-- init_memory_8_0_3; original full-tree equality = T
example : initMemory (width := 8) 0 [.inl 0, .inr 0, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 1))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 1)))))) (.skip)))))))) := by rfl

-- init_memory_8_1_0; original full-tree equality = T
example : initMemory (width := 8) 1 [] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.skip))))) := by rfl

-- init_memory_8_1_1; original full-tree equality = T
example : initMemory (width := 8) 1 [.inl 17] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 1)))))) (.skip)))))) := by rfl

-- init_memory_8_1_2; original full-tree equality = T
example : initMemory (width := 8) 1 [.inr 0] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 1))))) (.skip)))))) := by rfl

-- init_memory_8_1_3; original full-tree equality = T
example : initMemory (width := 8) 1 [.inl 0, .inr 1, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 1 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 1))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 1)))))) (.skip)))))))) := by rfl

-- init_memory_8_23_0; original full-tree equality = T
example : initMemory (width := 8) 23 [] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.skip))))) := by rfl

-- init_memory_8_23_1; original full-tree equality = T
example : initMemory (width := 8) 23 [.inl 17] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 1)))))) (.skip)))))) := by rfl

-- init_memory_8_23_2; original full-tree equality = T
example : initMemory (width := 8) 23 [.inr 0] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 1))))) (.skip)))))) := by rfl

-- init_memory_8_23_3; original full-tree equality = T
example : initMemory (width := 8) 23 [.inl 0, .inr 23, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 23 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 1))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 1)))))) (.skip)))))))) := by rfl

-- init_memory_8_1208925819614629174706185_0; original full-tree equality = T
example : initMemory (width := 8) 1208925819614629174706185 [] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.skip))))) := by rfl

-- init_memory_8_1208925819614629174706185_1; original full-tree equality = T
example : initMemory (width := 8) 1208925819614629174706185 [.inl 17] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 1)))))) (.skip)))))) := by rfl

-- init_memory_8_1208925819614629174706185_2; original full-tree equality = T
example : initMemory (width := 8) 1208925819614629174706185 [.inr 0] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 1))))) (.skip)))))) := by rfl

-- init_memory_8_1208925819614629174706185_3; original full-tree equality = T
example : initMemory (width := 8) 1208925819614629174706185 [.inl 0, .inr 1208925819614629174706185, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 1)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 1)))))) (.seq (.seq (.inst (.mem .store 1208925819614629174706185 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 1))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 1)))))) (.skip)))))))) := by rfl

-- init_memory_64_0_0; original full-tree equality = T
example : initMemory (width := 64) 0 [] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.skip))))) := by rfl

-- init_memory_64_0_1; original full-tree equality = T
example : initMemory (width := 64) 0 [.inl 17] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 8)))))) (.skip)))))) := by rfl

-- init_memory_64_0_2; original full-tree equality = T
example : initMemory (width := 64) 0 [.inr 0] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 8))))) (.skip)))))) := by rfl

-- init_memory_64_0_3; original full-tree equality = T
example : initMemory (width := 64) 0 [.inl 0, .inr 0, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 8))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 8)))))) (.skip)))))))) := by rfl

-- init_memory_64_1_0; original full-tree equality = T
example : initMemory (width := 64) 1 [] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.skip))))) := by rfl

-- init_memory_64_1_1; original full-tree equality = T
example : initMemory (width := 64) 1 [.inl 17] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 8)))))) (.skip)))))) := by rfl

-- init_memory_64_1_2; original full-tree equality = T
example : initMemory (width := 64) 1 [.inr 0] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 8))))) (.skip)))))) := by rfl

-- init_memory_64_1_3; original full-tree equality = T
example : initMemory (width := 64) 1 [.inl 0, .inr 1, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 1 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 8))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 8)))))) (.skip)))))))) := by rfl

-- init_memory_64_23_0; original full-tree equality = T
example : initMemory (width := 64) 23 [] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.skip))))) := by rfl

-- init_memory_64_23_1; original full-tree equality = T
example : initMemory (width := 64) 23 [.inl 17] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 8)))))) (.skip)))))) := by rfl

-- init_memory_64_23_2; original full-tree equality = T
example : initMemory (width := 64) 23 [.inr 0] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 8))))) (.skip)))))) := by rfl

-- init_memory_64_23_3; original full-tree equality = T
example : initMemory (width := 64) 23 [.inl 0, .inr 23, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 23 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 8))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 8)))))) (.skip)))))))) := by rfl

-- init_memory_64_1208925819614629174706185_0; original full-tree equality = T
example : initMemory (width := 64) 1208925819614629174706185 [] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.skip))))) := by rfl

-- init_memory_64_1208925819614629174706185_1; original full-tree equality = T
example : initMemory (width := 64) 1208925819614629174706185 [.inl 17] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 8)))))) (.skip)))))) := by rfl

-- init_memory_64_1208925819614629174706185_2; original full-tree equality = T
example : initMemory (width := 64) 1208925819614629174706185 [.inr 0] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 8))))) (.skip)))))) := by rfl

-- init_memory_64_1208925819614629174706185_3; original full-tree equality = T
example : initMemory (width := 64) 1208925819614629174706185 [.inl 0, .inr 1208925819614629174706185, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 8)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 8)))))) (.seq (.seq (.inst (.mem .store 1208925819614629174706185 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 8))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 8)))))) (.skip)))))))) := by rfl

-- init_memory_80_0_0; original full-tree equality = T
example : initMemory (width := 80) 0 [] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.skip))))) := by rfl

-- init_memory_80_0_1; original full-tree equality = T
example : initMemory (width := 80) 0 [.inl 17] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 10)))))) (.skip)))))) := by rfl

-- init_memory_80_0_2; original full-tree equality = T
example : initMemory (width := 80) 0 [.inr 0] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 10))))) (.skip)))))) := by rfl

-- init_memory_80_0_3; original full-tree equality = T
example : initMemory (width := 80) 0 [.inl 0, .inr 0, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 0 0 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 0 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 10))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.inst (.arith (.binop .add 1 1 (.imm 10)))))) (.skip)))))))) := by rfl

-- init_memory_80_1_0; original full-tree equality = T
example : initMemory (width := 80) 1 [] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.skip))))) := by rfl

-- init_memory_80_1_1; original full-tree equality = T
example : initMemory (width := 80) 1 [.inl 17] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 10)))))) (.skip)))))) := by rfl

-- init_memory_80_1_2; original full-tree equality = T
example : initMemory (width := 80) 1 [.inr 0] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 10))))) (.skip)))))) := by rfl

-- init_memory_80_1_3; original full-tree equality = T
example : initMemory (width := 80) 1 [.inl 0, .inr 1, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1 1 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 1 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 10))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 2 0))) (.inst (.arith (.binop .add 2 2 (.imm 10)))))) (.skip)))))))) := by rfl

-- init_memory_80_23_0; original full-tree equality = T
example : initMemory (width := 80) 23 [] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.skip))))) := by rfl

-- init_memory_80_23_1; original full-tree equality = T
example : initMemory (width := 80) 23 [.inl 17] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 10)))))) (.skip)))))) := by rfl

-- init_memory_80_23_2; original full-tree equality = T
example : initMemory (width := 80) 23 [.inr 0] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 10))))) (.skip)))))) := by rfl

-- init_memory_80_23_3; original full-tree equality = T
example : initMemory (width := 80) 23 [.inl 0, .inr 23, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 23 23 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 23 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 23 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 10))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 24 0))) (.inst (.arith (.binop .add 24 24 (.imm 10)))))) (.skip)))))))) := by rfl

-- init_memory_80_1208925819614629174706185_0; original full-tree equality = T
example : initMemory (width := 80) 1208925819614629174706185 [] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.skip))))) := by rfl

-- init_memory_80_1208925819614629174706185_1; original full-tree equality = T
example : initMemory (width := 80) 1208925819614629174706185 [.inl 17] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 17)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 10)))))) (.skip)))))) := by rfl

-- init_memory_80_1208925819614629174706185_2; original full-tree equality = T
example : initMemory (width := 80) 1208925819614629174706185 [.inr 0] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 10))))) (.skip)))))) := by rfl

-- init_memory_80_1208925819614629174706185_3; original full-tree equality = T
example : initMemory (width := 80) 1208925819614629174706185 [.inl 0, .inr 1208925819614629174706185, .inl 1208925819614629174706185] =
    (.seq (.inst (.const 0 10)) (.seq (.inst (.arith (.binop .sub 1208925819614629174706185 1208925819614629174706185 (.reg 0)))) (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706185 0))) (.seq (.seq (.inst (.const 0 0)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 10)))))) (.seq (.seq (.inst (.mem .store 1208925819614629174706185 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 10))))) (.seq (.seq (.inst (.const 0 9)) (.seq (.inst (.mem .store 0 (.addr 1208925819614629174706186 0))) (.inst (.arith (.binop .add 1208925819614629174706186 1208925819614629174706186 (.imm 10)))))) (.skip)))))))) := by rfl

end Flapjack.Test.StackRemoveInitMemory
