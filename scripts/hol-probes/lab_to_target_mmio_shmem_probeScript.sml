load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _=capture "mmio_pcs_min_index_APPEND_thm" mmio_pcs_min_index_APPEND_thm;
val _=types "mmio_pcs_min_index_APPEND_thm_types" mmio_pcs_min_index_APPEND_thm;
val _=print("mmio_pcs_min_index_APPEND_thm_hypotheses="^Int.toString(length(hyp mmio_pcs_min_index_APPEND_thm))^"\n");
val _=capture "mmio_pcs_min_index_get_shmem_info_ok" mmio_pcs_min_index_get_shmem_info_ok;
val _=types "mmio_pcs_min_index_get_shmem_info_ok_types" mmio_pcs_min_index_get_shmem_info_ok;
val _=print("mmio_pcs_min_index_get_shmem_info_ok_hypotheses="^Int.toString(length(hyp mmio_pcs_min_index_get_shmem_info_ok))^"\n");
val _=show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val template = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (-128w,127w); hw_offset := (-128w,127w); byte_offset := (-128w,127w);
 jump_offset := (-128w,127w); cjump_offset := (-128w,127w); loc_offset := (-128w,127w)
 |> : 8 asm_config``;
val cfg = ``^template with <|code_alignment:=1;encode:=(λa.[0w;0w])|>``;
val old = ``fromAList [(1,fromAList [(7,20:num)])]``;
val extra = ``insert 99 (fromAList [(8,24:num)]) ^old``;
val code=``[Section 0 [];Section 1 [Label 1 7 0;Asm (ShareMem Load8 3 (Addr 2 5w)) [0w;0w] 2;Asm (Cbw 1 2) [0w;0w] 2;LabAsm (Jump (Lab 1 7)) 99w [0w;0w] 2;Label 1 7 0];Section 2 [Asm (ShareMem Store8 4 (Addr 2 (-1w))) [0w;0w] 2;Asm (Asmi (Inst Skip)) [0w;0w] 2];Section 0 []]:8 sec list``;
val names=``[SharedMem MappedWrite]``;
val initial=``<|entry_pc:=100;nbytes:=3w;addr_reg:=99;addr_off:=42;reg:=77;exit_pc:=103|>``;
val loadinfo=``<|entry_pc:=7;nbytes:=1w;addr_reg:=2;addr_off:=5;reg:=3;exit_pc:=9|>``;
val storeinfo=``<|entry_pc:=13;nbytes:=1w;addr_reg:=2;addr_off:=255;reg:=4;exit_pc:=15|>``;
fun checked label th=(print(label^"=");print_term(rhs(concl(EQT_INTRO th)));print"\n");
fun observe label q=checked label (prove(q, simp [] >> EVAL_TAC >> simp []));
fun discharge th = MP th (prove(fst(dest_imp(concl th)), simp [] >> EVAL_TAC >> simp []));
fun appendCase label prefix suffix = checked label (discharge (INST [``ffis:ffiname list`` |-> prefix,``l:ffiname list`` |-> suffix] mmio_pcs_min_index_APPEND_thm));
val guest=``ExtCall(strlit "guest")``;
val _=appendCase "empty_boundary" ``[]:ffiname list`` ``[]:ffiname list``;
val _=appendCase "external_boundary" ``[^guest]`` ``[]:ffiname list``;
val _=appendCase "shared_boundary" ``[]:ffiname list`` ``[SharedMem MappedRead]``;
val _=appendCase "mixed_boundary" ``[^guest;^guest]`` ``[SharedMem MappedRead;SharedMem MappedWrite]``;
val _=observe "suffix_guard" ``~EVERY (λx.∀s.x<>ExtCall s) [^guest]``;
val _=observe "prefix_guard" ``~EVERY (λx.∃s.x=ExtCall s) [SharedMem MappedRead]``;
val ex=INST_TYPE [``:'a`` |-> ``:8``] mmio_pcs_min_index_get_shmem_info_ok;
val inputs=[mk_var("c",type_of cfg) |-> cfg,mk_var("labs",type_of old)|->old,
  ``ffis':ffiname list`` |-> ``[]:ffiname list``,``p':num`` |-> ``18:num``,
  ``code2:8 sec list`` |-> code,``ffis:ffiname list`` |-> ``[^guest]``,
  ``p:num`` |-> ``7:num``,``new_ffi_names:ffiname list`` |-> ``[^guest;SharedMem MappedRead;SharedMem MappedWrite]``,
  ``new_shmem_info:shmem_info_num list`` |-> ``[^loadinfo;^storeinfo]``];
val _=checked "extraction_boundary" (discharge (INST inputs ex));
