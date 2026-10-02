import Flapjack.RiscV.L3.Defs.MMU.Walk
namespace Flapjack.Test
open Flapjack.RiscV.L3
set_option maxRecDepth 200000

-- Original oracle walk_invalid: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (0 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (none,0,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_pointer_zero: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (1025 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (none,1025,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_pointer_type_one: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (1027 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (none,1027,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_read: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3111,0,false,0),3111,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_write: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Write, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3175,0,false,0),3175,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_already_rd: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3175 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Instruction, accessType.Write, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3175,0,false,0),3175,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_permission_denied: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3077 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Write, Privilege.User, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (none,3077,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_global: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3103 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.Supervisor, (0:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3135,0,true,0),3135,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_superpage_unaligned_ppn: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((5752:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 1) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (5752,3111,1,false,0),3111,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_pointer_leaf: complete result payload and both PTE memory words.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (1025 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (3079 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 1) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3111,0,false,4096),1025,3111) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_level4: literal width/level/address boundary.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 4) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (0,3111,4,false,0),3111,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_leaf_level1000: literal width/level/address boundary.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 1000) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (0,3111,1000,false,0),3111,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_recursive_ppn_truncated: literal width/level/address boundary.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (68719476737 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 1) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (none,68719476737,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_pointer_type_one_leaf: literal width/level/address boundary.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (1027 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (3079 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((0:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (0:BitVec 64), 1) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3111,0,false,4096),1027,3111) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

-- Original oracle walk_pte_address_wrap: literal width/level/address boundary.
example : (let s := { (default : riscv_state) with MEM8 := (fun adr : BitVec 64 => if adr.toNat < 8 then BitVec.ofNat 8 (3079 / (2 ^ (8 * adr.toNat))) else if 4096 ≤ adr.toNat ∧ adr.toNat < 4104 then BitVec.ofNat 8 (0 / (2 ^ (8 * (adr.toNat - 4096)))) else 0) }; let r := walk64 ((4096:BitVec 64), fetchType.Data, accessType.Read, Privilege.User, (18446744073709551608:BitVec 64), 0) s; (r.1.map (fun (pa,p,l,g,a) => (pa.toNat, («reg'SV_PTE» p).toNat, l, g, a.toNat)), (rawReadData 0 r.2).toNat, (rawReadData 4096 r.2).toNat)) = (some (12288,3111,0,false,0),3111,0) := by
  simp [walk64, rawReadData, rawWriteData, MEM, «write'MEM», «rec'SV_Vaddr», «rec'SV_PTE», «reg'SV_PTE», checkMemPermission, isGlobal, LEVEL_BITS, PAGESIZE_BITS, holWordExtract, holUpdate] <;> decide

end Flapjack.Test
