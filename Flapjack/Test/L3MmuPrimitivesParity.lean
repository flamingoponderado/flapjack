import Flapjack.RiscV.L3.Defs.MMU.Primitives

set_option maxRecDepth 10000
namespace Flapjack.Test
open Flapjack.RiscV.L3
-- Original oracle privilege_0
example : privilege (0 : BitVec 2) = Privilege.User := by simp [privilege]
-- Original oracle privilege_1
example : privilege (1 : BitVec 2) = Privilege.Supervisor := by simp [privilege]
-- Original oracle privilege_2
example : privilege (2 : BitVec 2) = Privilege.Hypervisor := by simp [privilege]
-- Original oracle privilege_3
example : privilege (3 : BitVec 2) = Privilege.Machine := by simp [privilege]
-- Original oracle mem_write_full
example (v : BitVec 64) (a : BitVec 61) (s : riscv_state) :
    «write'MEM» (v,a) s =
      (let b : BitVec 64 := a.setWidth 64 <<< 3
       { s with MEM8 := holUpdate b (holWordExtract 8 7 0 v) (holUpdate (b + (1 : BitVec 64)) (holWordExtract 8 15 8 v) (holUpdate (b + (2 : BitVec 64)) (holWordExtract 8 23 16 v) (holUpdate (b + (3 : BitVec 64)) (holWordExtract 8 31 24 v) (holUpdate (b + (4 : BitVec 64)) (holWordExtract 8 39 32 v) (holUpdate (b + (5 : BitVec 64)) (holWordExtract 8 47 40 v) (holUpdate (b + (6 : BitVec 64)) (holWordExtract 8 55 48 v) (holUpdate (b + (7 : BitVec 64)) (holWordExtract 8 63 56 v) (s.MEM8)))))))) }) := by rfl

-- Original oracle mem_read_0
example : (MEM (0 : BitVec 61) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 506097522914230528 := by decide
-- Original oracle mem_read_1
example : (MEM (1 : BitVec 61) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 1084818905618843912 := by decide
-- Original oracle mem_read_2
example : (MEM (31 : BitVec 61) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 18446460386757245432 := by decide
-- Original oracle mem_read_3
example : (MEM (2305843009213693951 : BitVec 61) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 18446460386757245432 := by decide

end Flapjack.Test
