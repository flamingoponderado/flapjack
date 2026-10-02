import Flapjack.RiscV.L3.Defs.MMU.Access
set_option maxRecDepth 10000
namespace Flapjack.Test
open Flapjack.RiscV.L3
example : (rawReadData (0 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 506097522914230528 := by decide
example : (rawReadData (1 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 578437695752307201 := by decide
example : (rawReadData (2 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 650777868590383874 := by decide
example : (rawReadData (3 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 723118041428460547 := by decide
example : (rawReadData (4 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 795458214266537220 := by decide
example : (rawReadData (5 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 867798387104613893 := by decide
example : (rawReadData (6 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 940138559942690566 := by decide
example : (rawReadData (7 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 1012478732780767239 := by decide
example : (rawReadData (248 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 18446460386757245432 := by decide
example : (rawReadData (249 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 72056485885770489 := by decide
example : (rawReadData (18446744073709551615 : BitVec 64) { (default : riscv_state) with MEM8 := fun adr => BitVec.ofNat 8 adr.toNat }).toNat = 433757350076154111 := by decide

-- Original oracle perm_2_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(2:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(2:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(2:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(2:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(2:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_2_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(2:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(3:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_3_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(3:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(4:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(4:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(4:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(4:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_4_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(4:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(5:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_5_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(5:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(6:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_6_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(6:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_7_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(7:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(8:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(8:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(8:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_8_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(8:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(9:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_9_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(9:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(10:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_10_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(10:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(11:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(11:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(11:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(11:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_11_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(11:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(12:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(12:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(12:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_12_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(12:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(13:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_13_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(13:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(14:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_14_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(14:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.User,(15:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Supervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Hypervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Read,Privilege.Machine,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.User,(15:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Supervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Hypervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Instruction_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Instruction,accessType.Write,Privilege.Machine,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Read_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.User,(15:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Read_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Supervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Read_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Hypervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Read_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Read,Privilege.Machine,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Write_User
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.User,(15:BitVec 4)) state = (false,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Write_Supervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Supervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Write_Hypervisor
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Hypervisor,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
-- Original oracle perm_15_Data_Write_Machine
example (state : riscv_state) : checkMemPermission (fetchType.Data,accessType.Write,Privilege.Machine,(15:BitVec 4)) state = (true,state) := by simp [checkMemPermission]
example (state:riscv_state) : vmType (0:BitVec 5) state = (VM_Mode.Mbare,state) := by simp [vmType]
example (state:riscv_state) : vmType (1:BitVec 5) state = (VM_Mode.Mbb,state) := by simp [vmType]
example (state:riscv_state) : vmType (2:BitVec 5) state = (VM_Mode.Mbbid,state) := by simp [vmType]
example (state:riscv_state) : vmType (8:BitVec 5) state = (VM_Mode.Sv32,state) := by simp [vmType]
example (state:riscv_state) : vmType (9:BitVec 5) state = (VM_Mode.Sv39,state) := by simp [vmType]
example (state:riscv_state) : vmType (10:BitVec 5) state = (VM_Mode.Sv48,state) := by simp [vmType]
example (state:riscv_state) : vmType (11:BitVec 5) state = (VM_Mode.Sv57,state) := by simp [vmType]
example (state:riscv_state) : vmType (12:BitVec 5) state = (VM_Mode.Sv64,state) := by simp [vmType]

example (ft:fetchType)(ac:accessType)(priv:Privilege)(s:riscv_state) : checkMemPermission (ft,ac,priv,(0:BitVec 4)) s = «raise'exception» (exception.INTERNAL_ERROR [67, 104, 101, 99, 107, 105, 110, 103, 32, 112, 101, 114, 109, 32, 111, 110, 32, 80, 97, 103, 101, 45, 84, 97, 98, 108, 101, 32, 112, 111, 105, 110, 116, 101, 114, 33]) s := by simp [checkMemPermission]
example (ft:fetchType)(ac:accessType)(priv:Privilege)(s:riscv_state) : checkMemPermission (ft,ac,priv,(1:BitVec 4)) s = «raise'exception» (exception.INTERNAL_ERROR [67, 104, 101, 99, 107, 105, 110, 103, 32, 112, 101, 114, 109, 32, 111, 110, 32, 80, 97, 103, 101, 45, 84, 97, 98, 108, 101, 32, 112, 111, 105, 110, 116, 101, 114, 33]) s := by simp [checkMemPermission]
example (s:riscv_state) : vmType (3:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 51]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (4:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 52]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (5:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 53]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (6:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 54]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (7:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 55]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (13:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 51]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (14:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 52]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (15:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 53]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (16:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 54]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (17:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 55]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (18:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 56]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (19:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 49, 57]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (20:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 48]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (21:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 49]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (22:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 50]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (23:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 51]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (24:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 52]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (25:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 53]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (26:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 54]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (27:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 55]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (28:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 56]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (29:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 50, 57]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (30:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 51, 48]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s:riscv_state) : vmType (31:BitVec 5) s = «raise'exception» (exception.UNDEFINED [85, 110, 107, 110, 111, 119, 110, 32, 97, 100, 100, 114, 101, 115, 115, 32, 116, 114, 97, 110, 115, 108, 97, 116, 105, 111, 110, 32, 109, 111, 100, 101, 58, 32, 51, 49]) s := by simp [vmType,Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]

-- Original oracle write_0_0
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),0) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_0_1
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),1) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 136, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_0_2
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),2) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 136, 119, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_0_8
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),8) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 136, 119, 102, 85, 68, 51, 34, 17, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_0_9
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),9) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 136, 119, 102, 85, 68, 51, 34, 17, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_0_16
example : (let s := rawWriteData ((0:BitVec 64),(1234605616436508552:BitVec 64),16) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((0:BitVec 64) - 1)).toNat, (s.MEM8 ((0:BitVec 64)+0)).toNat, (s.MEM8 ((0:BitVec 64)+1)).toNat, (s.MEM8 ((0:BitVec 64)+2)).toNat, (s.MEM8 ((0:BitVec 64)+3)).toNat, (s.MEM8 ((0:BitVec 64)+4)).toNat, (s.MEM8 ((0:BitVec 64)+5)).toNat, (s.MEM8 ((0:BitVec 64)+6)).toNat, (s.MEM8 ((0:BitVec 64)+7)).toNat, (s.MEM8 ((0:BitVec 64)+8)).toNat, (s.MEM8 ((0:BitVec 64)+9)).toNat, (s.MEM8 ((0:BitVec 64)+10)).toNat, (s.MEM8 ((0:BitVec 64)+11)).toNat, (s.MEM8 ((0:BitVec 64)+12)).toNat, (s.MEM8 ((0:BitVec 64)+13)).toNat, (s.MEM8 ((0:BitVec 64)+14)).toNat, (s.MEM8 ((0:BitVec 64)+15)).toNat]) = [255, 136, 119, 102, 85, 68, 51, 34, 17, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
-- Original oracle write_1_0
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),0) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_1_1
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),1) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 136, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_1_2
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),2) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 136, 119, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_1_8
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),8) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 136, 119, 102, 85, 68, 51, 34, 17, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_1_9
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),9) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 136, 119, 102, 85, 68, 51, 34, 17, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_1_16
example : (let s := rawWriteData ((7:BitVec 64),(1234605616436508552:BitVec 64),16) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((7:BitVec 64) - 1)).toNat, (s.MEM8 ((7:BitVec 64)+0)).toNat, (s.MEM8 ((7:BitVec 64)+1)).toNat, (s.MEM8 ((7:BitVec 64)+2)).toNat, (s.MEM8 ((7:BitVec 64)+3)).toNat, (s.MEM8 ((7:BitVec 64)+4)).toNat, (s.MEM8 ((7:BitVec 64)+5)).toNat, (s.MEM8 ((7:BitVec 64)+6)).toNat, (s.MEM8 ((7:BitVec 64)+7)).toNat, (s.MEM8 ((7:BitVec 64)+8)).toNat, (s.MEM8 ((7:BitVec 64)+9)).toNat, (s.MEM8 ((7:BitVec 64)+10)).toNat, (s.MEM8 ((7:BitVec 64)+11)).toNat, (s.MEM8 ((7:BitVec 64)+12)).toNat, (s.MEM8 ((7:BitVec 64)+13)).toNat, (s.MEM8 ((7:BitVec 64)+14)).toNat, (s.MEM8 ((7:BitVec 64)+15)).toNat]) = [6, 136, 119, 102, 85, 68, 51, 34, 17, 15, 16, 17, 18, 19, 20, 21, 22] := by decide
-- Original oracle write_2_0
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),0) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
-- Original oracle write_2_1
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),1) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 136, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
-- Original oracle write_2_2
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),2) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 136, 119, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
-- Original oracle write_2_8
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),8) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 136, 119, 102, 85, 68, 51, 34, 17, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
-- Original oracle write_2_9
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),9) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 136, 119, 102, 85, 68, 51, 34, 17, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
-- Original oracle write_2_16
example : (let s := rawWriteData ((18446744073709551615:BitVec 64),(1234605616436508552:BitVec 64),16) { (default:riscv_state) with MEM8:=fun adr=>BitVec.ofNat 8 adr.toNat }; [(s.MEM8 ((18446744073709551615:BitVec 64) - 1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+0)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+1)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+2)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+3)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+4)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+5)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+6)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+7)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+8)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+9)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+10)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+11)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+12)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+13)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+14)).toNat, (s.MEM8 ((18446744073709551615:BitVec 64)+15)).toNat]) = [254, 136, 119, 102, 85, 68, 51, 34, 17, 7, 8, 9, 10, 11, 12, 13, 14] := by decide

example (s:riscv_state) : curASID () s = holWordExtract 6 5 0 (s.c_SCSR s.procID).sasid := by rfl
end Flapjack.Test
