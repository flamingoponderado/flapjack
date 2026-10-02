load "riscvTheory"; load "wordsLib"; load "blastLib";
open HolKernel Parse bossLib Tactical boolSyntax Conv riscvTheory;
val _ = Globals.linewidth := 100000;
val defs = [privilege_def,SCSR_def,ASID_SIZE_def,reg'SV_PTE_def,MEM_def,write'MEM_def,TLB_def,write'TLB_def,rec'SV_Vaddr_def,LEVEL_BITS_def,rec'SV_PTE_def,isGlobal_def,PAGESIZE_BITS_def,TLBEntries_def];
val _ = computeLib.add_funs defs;
fun out label q = let val th = (EVAL THENC wordsLib.WORD_EVAL_CONV THENC EVAL) q in
 if null(hyp th) then (print(label ^ "="); print_term(snd(dest_eq(concl th))); print "\n")
 else raise Fail "undischarged assumptions" end;
fun equation label q = let val th = prove(q,SIMP_TAC (srw_ss() ++ wordsLib.WORD_EXTRACT_ss) (boolTheory.LET_THM::defs)) in
 if null(hyp th) then (print(label ^ "="); print_thm th; print "\n")
 else raise Fail "undischarged assumptions" end;
val _ = out "constant_ASID_SIZE" ``ASID_SIZE``;
val _ = out "constant_LEVEL_BITS" ``LEVEL_BITS``;
val _ = out "constant_PAGESIZE_BITS" ``PAGESIZE_BITS``;
val _ = out "constant_TLBEntries" ``TLBEntries``;
val _ = out "privilege_0" ``privilege 0w``;
val _ = out "privilege_1" ``privilege 1w``;
val _ = out "privilege_2" ``privilege 2w``;
val _ = out "privilege_3" ``privilege 3w``;
val _ = out "global_0" ``isGlobal 0w``;
val _ = out "global_1" ``isGlobal 1w``;
val _ = out "global_2" ``isGlobal 2w``;
val _ = out "global_3" ``isGlobal 3w``;
val _ = out "global_4" ``isGlobal 4w``;
val _ = out "global_5" ``isGlobal 5w``;
val _ = out "global_6" ``isGlobal 6w``;
val _ = out "global_7" ``isGlobal 7w``;
val _ = out "global_8" ``isGlobal 8w``;
val _ = out "global_9" ``isGlobal 9w``;
val _ = out "global_10" ``isGlobal 10w``;
val _ = out "global_11" ``isGlobal 11w``;
val _ = out "global_12" ``isGlobal 12w``;
val _ = out "global_13" ``isGlobal 13w``;
val _ = out "global_14" ``isGlobal 14w``;
val _ = out "global_15" ``isGlobal 15w``;
val _ = out "pte_0" ``let r = rec'SV_PTE (0w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_0" ``w2n (reg'SV_PTE (rec'SV_PTE (0w:64 word)))``;
val _ = out "vaddr_0" ``let r = rec'SV_Vaddr (0w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_1" ``let r = rec'SV_PTE (1w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_1" ``w2n (reg'SV_PTE (rec'SV_PTE (1w:64 word)))``;
val _ = out "vaddr_1" ``let r = rec'SV_Vaddr (1w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_2" ``let r = rec'SV_PTE (32w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_2" ``w2n (reg'SV_PTE (rec'SV_PTE (32w:64 word)))``;
val _ = out "vaddr_2" ``let r = rec'SV_Vaddr (32w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_3" ``let r = rec'SV_PTE (64w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_3" ``w2n (reg'SV_PTE (rec'SV_PTE (64w:64 word)))``;
val _ = out "vaddr_3" ``let r = rec'SV_Vaddr (64w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_4" ``let r = rec'SV_PTE (127w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_4" ``w2n (reg'SV_PTE (rec'SV_PTE (127w:64 word)))``;
val _ = out "vaddr_4" ``let r = rec'SV_Vaddr (127w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_5" ``let r = rec'SV_PTE (255w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_5" ``w2n (reg'SV_PTE (rec'SV_PTE (255w:64 word)))``;
val _ = out "vaddr_5" ``let r = rec'SV_Vaddr (255w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_6" ``let r = rec'SV_PTE (1023w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_6" ``w2n (reg'SV_PTE (rec'SV_PTE (1023w:64 word)))``;
val _ = out "vaddr_6" ``let r = rec'SV_Vaddr (1023w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_7" ``let r = rec'SV_PTE (1024w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_7" ``w2n (reg'SV_PTE (rec'SV_PTE (1024w:64 word)))``;
val _ = out "vaddr_7" ``let r = rec'SV_Vaddr (1024w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_8" ``let r = rec'SV_PTE (1311768467463790320w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_8" ``w2n (reg'SV_PTE (rec'SV_PTE (1311768467463790320w:64 word)))``;
val _ = out "vaddr_8" ``let r = rec'SV_Vaddr (1311768467463790320w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = out "pte_9" ``let r = rec'SV_PTE (18446744073709551615w:64 word) in (if r.PTE_D then 1 else 0,w2n r.PTE_PPNi,if r.PTE_R then 1 else 0,w2n r.PTE_SW,w2n r.PTE_T,if r.PTE_V then 1 else 0,w2n r.sv_pte'rst)``;
val _ = out "pte_repack_9" ``w2n (reg'SV_PTE (rec'SV_PTE (18446744073709551615w:64 word)))``;
val _ = out "vaddr_9" ``let r = rec'SV_Vaddr (18446744073709551615w:64 word) in (w2n r.Sv_PgOfs,w2n r.Sv_VPNi,w2n r.sv_vaddr'rst)``;
val _ = equation "scsr_full" ``SCSR s = s.c_SCSR s.procID``;
val _ = equation "tlb_full" ``TLB s = s.c_tlb s.procID``;
val _ = equation "tlb_write_full" ``write'TLB value s = s with c_tlb := (s.procID =+ value) s.c_tlb``;
val _ = equation "mem_write_full" ``let b = (w2w a :64 word) << 3 in write'MEM (v,a) s = s with MEM8 := ((b + 0w =+ ((7><0) v : 8 word)) ((b + 1w =+ ((15><8) v : 8 word)) ((b + 2w =+ ((23><16) v : 8 word)) ((b + 3w =+ ((31><24) v : 8 word)) ((b + 4w =+ ((39><32) v : 8 word)) ((b + 5w =+ ((47><40) v : 8 word)) ((b + 6w =+ ((55><48) v : 8 word)) ((b + 7w =+ ((63><56) v : 8 word)) s.MEM8))))))))``;

val _ = out "mem_read_0" ``w2n (MEM (0w:61 word) ((ARB:riscv_state) with MEM8 := (\adr. n2w(w2n adr))))``;

val _ = out "mem_read_1" ``w2n (MEM (1w:61 word) ((ARB:riscv_state) with MEM8 := (\adr. n2w(w2n adr))))``;

val _ = out "mem_read_2" ``w2n (MEM (31w:61 word) ((ARB:riscv_state) with MEM8 := (\adr. n2w(w2n adr))))``;

val _ = out "mem_read_3" ``w2n (MEM (2305843009213693951w:61 word) ((ARB:riscv_state) with MEM8 := (\adr. n2w(w2n adr))))``;
