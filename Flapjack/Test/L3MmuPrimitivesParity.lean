import Flapjack.RiscV.L3.Defs.MMU.Primitives

set_option maxRecDepth 10000
namespace Flapjack.Test
open Flapjack.RiscV.L3
-- Original oracle constant_ASID_SIZE
example : ASID_SIZE = 6 := by decide
-- Original oracle constant_LEVEL_BITS
example : LEVEL_BITS = 9 := by decide
-- Original oracle constant_PAGESIZE_BITS
example : PAGESIZE_BITS = 12 := by decide
-- Original oracle constant_TLBEntries
example : TLBEntries = 16 := by decide
-- Original oracle privilege_0
example : privilege (0 : BitVec 2) = Privilege.User := by simp [privilege]
-- Original oracle privilege_1
example : privilege (1 : BitVec 2) = Privilege.Supervisor := by simp [privilege]
-- Original oracle privilege_2
example : privilege (2 : BitVec 2) = Privilege.Hypervisor := by simp [privilege]
-- Original oracle privilege_3
example : privilege (3 : BitVec 2) = Privilege.Machine := by simp [privilege]
-- Original oracle global_0
example : isGlobal (0 : BitVec 4) = false := by decide
-- Original oracle global_1
example : isGlobal (1 : BitVec 4) = false := by decide
-- Original oracle global_2
example : isGlobal (2 : BitVec 4) = false := by decide
-- Original oracle global_3
example : isGlobal (3 : BitVec 4) = false := by decide
-- Original oracle global_4
example : isGlobal (4 : BitVec 4) = false := by decide
-- Original oracle global_5
example : isGlobal (5 : BitVec 4) = false := by decide
-- Original oracle global_6
example : isGlobal (6 : BitVec 4) = false := by decide
-- Original oracle global_7
example : isGlobal (7 : BitVec 4) = false := by decide
-- Original oracle global_8
example : isGlobal (8 : BitVec 4) = false := by decide
-- Original oracle global_9
example : isGlobal (9 : BitVec 4) = false := by decide
-- Original oracle global_10
example : isGlobal (10 : BitVec 4) = false := by decide
-- Original oracle global_11
example : isGlobal (11 : BitVec 4) = false := by decide
-- Original oracle global_12
example : isGlobal (12 : BitVec 4) = true := by decide
-- Original oracle global_13
example : isGlobal (13 : BitVec 4) = true := by decide
-- Original oracle global_14
example : isGlobal (14 : BitVec 4) = true := by decide
-- Original oracle global_15
example : isGlobal (15 : BitVec 4) = true := by decide
-- Original oracle pte_0
example : (if («rec'SV_PTE» (0 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (0 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (0 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (0 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (0 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (0 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (0 : BitVec 64)).«sv_pte'rst».toNat) = (0, 0, 0, 0, 0, 0, 0) := by decide
-- Original oracle pte_repack_0
example : («reg'SV_PTE» («rec'SV_PTE» (0 : BitVec 64))).toNat = 0 := by decide
-- Original oracle vaddr_0
example : ((«rec'SV_Vaddr» (0 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (0 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (0 : BitVec 64)).«sv_vaddr'rst».toNat) = (0, 0, 0) := by decide
-- Original oracle pte_1
example : (if («rec'SV_PTE» (1 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (1 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (1 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (1 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (1 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (1 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (1 : BitVec 64)).«sv_pte'rst».toNat) = (0, 0, 0, 0, 0, 1, 0) := by decide
-- Original oracle pte_repack_1
example : («reg'SV_PTE» («rec'SV_PTE» (1 : BitVec 64))).toNat = 1 := by decide
-- Original oracle vaddr_1
example : ((«rec'SV_Vaddr» (1 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (1 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (1 : BitVec 64)).«sv_vaddr'rst».toNat) = (1, 0, 0) := by decide
-- Original oracle pte_2
example : (if («rec'SV_PTE» (32 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (32 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (32 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (32 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (32 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (32 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (32 : BitVec 64)).«sv_pte'rst».toNat) = (0, 0, 1, 0, 0, 0, 0) := by decide
-- Original oracle pte_repack_2
example : («reg'SV_PTE» («rec'SV_PTE» (32 : BitVec 64))).toNat = 32 := by decide
-- Original oracle vaddr_2
example : ((«rec'SV_Vaddr» (32 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (32 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (32 : BitVec 64)).«sv_vaddr'rst».toNat) = (32, 0, 0) := by decide
-- Original oracle pte_3
example : (if («rec'SV_PTE» (64 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (64 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (64 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (64 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (64 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (64 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (64 : BitVec 64)).«sv_pte'rst».toNat) = (1, 0, 0, 0, 0, 0, 0) := by decide
-- Original oracle pte_repack_3
example : («reg'SV_PTE» («rec'SV_PTE» (64 : BitVec 64))).toNat = 64 := by decide
-- Original oracle vaddr_3
example : ((«rec'SV_Vaddr» (64 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (64 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (64 : BitVec 64)).«sv_vaddr'rst».toNat) = (64, 0, 0) := by decide
-- Original oracle pte_4
example : (if («rec'SV_PTE» (127 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (127 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (127 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (127 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (127 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (127 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (127 : BitVec 64)).«sv_pte'rst».toNat) = (1, 0, 1, 0, 15, 1, 0) := by decide
-- Original oracle pte_repack_4
example : («reg'SV_PTE» («rec'SV_PTE» (127 : BitVec 64))).toNat = 127 := by decide
-- Original oracle vaddr_4
example : ((«rec'SV_Vaddr» (127 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (127 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (127 : BitVec 64)).«sv_vaddr'rst».toNat) = (127, 0, 0) := by decide
-- Original oracle pte_5
example : (if («rec'SV_PTE» (255 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (255 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (255 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (255 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (255 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (255 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (255 : BitVec 64)).«sv_pte'rst».toNat) = (1, 0, 1, 1, 15, 1, 0) := by decide
-- Original oracle pte_repack_5
example : («reg'SV_PTE» («rec'SV_PTE» (255 : BitVec 64))).toNat = 255 := by decide
-- Original oracle vaddr_5
example : ((«rec'SV_Vaddr» (255 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (255 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (255 : BitVec 64)).«sv_vaddr'rst».toNat) = (255, 0, 0) := by decide
-- Original oracle pte_6
example : (if («rec'SV_PTE» (1023 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (1023 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (1023 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (1023 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (1023 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (1023 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (1023 : BitVec 64)).«sv_pte'rst».toNat) = (1, 0, 1, 7, 15, 1, 0) := by decide
-- Original oracle pte_repack_6
example : («reg'SV_PTE» («rec'SV_PTE» (1023 : BitVec 64))).toNat = 1023 := by decide
-- Original oracle vaddr_6
example : ((«rec'SV_Vaddr» (1023 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (1023 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (1023 : BitVec 64)).«sv_vaddr'rst».toNat) = (1023, 0, 0) := by decide
-- Original oracle pte_7
example : (if («rec'SV_PTE» (1024 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (1024 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (1024 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (1024 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (1024 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (1024 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (1024 : BitVec 64)).«sv_pte'rst».toNat) = (0, 1, 0, 0, 0, 0, 0) := by decide
-- Original oracle pte_repack_7
example : («reg'SV_PTE» («rec'SV_PTE» (1024 : BitVec 64))).toNat = 1024 := by decide
-- Original oracle vaddr_7
example : ((«rec'SV_Vaddr» (1024 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (1024 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (1024 : BitVec 64)).«sv_vaddr'rst».toNat) = (1024, 0, 0) := by decide
-- Original oracle pte_8
example : (if («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (1311768467463790320 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (1311768467463790320 : BitVec 64)).«sv_pte'rst».toNat) = (1, 92847648567, 1, 5, 8, 0, 4660) := by decide
-- Original oracle pte_repack_8
example : («reg'SV_PTE» («rec'SV_PTE» (1311768467463790320 : BitVec 64))).toNat = 1311768467463790320 := by decide
-- Original oracle vaddr_8
example : ((«rec'SV_Vaddr» (1311768467463790320 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (1311768467463790320 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (1311768467463790320 : BitVec 64)).«sv_vaddr'rst».toNat) = (3824, 23211912141, 4660) := by decide
-- Original oracle pte_9
example : (if («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_D then 1 else 0, («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_PPNi.toNat, if («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_R then 1 else 0, («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_SW.toNat, («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_T.toNat, if («rec'SV_PTE» (18446744073709551615 : BitVec 64)).PTE_V then 1 else 0, («rec'SV_PTE» (18446744073709551615 : BitVec 64)).«sv_pte'rst».toNat) = (1, 274877906943, 1, 7, 15, 1, 65535) := by decide
-- Original oracle pte_repack_9
example : («reg'SV_PTE» («rec'SV_PTE» (18446744073709551615 : BitVec 64))).toNat = 18446744073709551615 := by decide
-- Original oracle vaddr_9
example : ((«rec'SV_Vaddr» (18446744073709551615 : BitVec 64)).Sv_PgOfs.toNat, («rec'SV_Vaddr» (18446744073709551615 : BitVec 64)).Sv_VPNi.toNat, («rec'SV_Vaddr» (18446744073709551615 : BitVec 64)).«sv_vaddr'rst».toNat) = (4095, 68719476735, 65535) := by decide
-- Original oracle scsr_full
example (s : riscv_state) : SCSR s = s.c_SCSR s.procID := by rfl
-- Original oracle tlb_full
example (s : riscv_state) : TLB s = s.c_tlb s.procID := by rfl
-- Original oracle tlb_write_full
example (value : BitVec 4 → Option TLBEntry) (s : riscv_state) : «write'TLB» value s = { s with c_tlb := holUpdate s.procID value s.c_tlb } := by rfl
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
