load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
(* Statements of the compile_correct code/oracle helpers.  Each statement is
   re-elaborated from the unchanged source text (^s1 expanded to its type
   annotation) so [local] and exported theorems are captured uniformly; these
   are statement captures, not theorem replays. *)
fun stmt label tm = (print(label ^ "="); print_term tm; print "\n");
fun stmt_types label tm =
 (show_types := true; stmt label tm; show_types := false);
val oracle_tie_shift_gen_tm = ``
  ∀mc_conf mc2 ms1 s1 ms2 l.
  oracle_tie mc_conf ms1 (s1:('a,'c,'ffi) labSem$state) ∧
  (∀k. find_next_interference mc_conf s1.ffi (k + l) ms1 =
       find_next_interference mc2 s1.ffi k ms2) ∧
  mc2.target = mc_conf.target ∧
  mc2.callee_saved_regs = mc_conf.callee_saved_regs ∧
  mc2.ptr_reg = mc_conf.ptr_reg ⇒
  oracle_tie mc2 ms2 s1
``;
val _ = stmt "oracle_tie_shift_gen" oracle_tie_shift_gen_tm;
val _ = stmt_types "oracle_tie_shift_gen_types" oracle_tie_shift_gen_tm;
val oracle_tie_ccache_residues_tm = ``
  ∀mc_conf mc2 ms1 s1 ms2 l t1.
  oracle_tie mc_conf ms1 (s1:('a,'c,'ffi) labSem$state) ∧
  (∀k. find_next_interference mc_conf s1.ffi (k + l) ms1 =
       find_next_interference mc2 s1.ffi k ms2) ∧
  mc2.target = mc_conf.target ∧
  mc2.ptr_reg = mc_conf.ptr_reg ∧
  mc2.len_reg = mc_conf.len_reg ∧
  mc2.ccache_interfer = mc_conf.ccache_interfer ∧
  mc2.target.get_pc ms2 ∉ mc2.prog_addresses DIFF set mc2.ffi_entry_pcs ∧
  mc2.target.get_pc ms2 ≠ mc2.halt_pc ∧
  mc2.target.get_pc ms2 = mc2.ccache_pc ⇒
  (λa. get_reg_value (s1.cc_regs 0 a) (t1.regs a) I) =
    (λa. if MEM a mc_conf.callee_saved_regs ∨ a = mc_conf.ptr_reg ∨
            ¬(a < mc_conf.target.config.reg_count) ∨
            MEM a mc_conf.target.config.avoid_regs
         then t1.regs a
         else mc_conf.target.get_reg
                (mc_conf.ccache_interfer 0
                   (mc_conf.target.get_reg ms2 mc_conf.ptr_reg,
                    mc_conf.target.get_reg ms2 mc_conf.len_reg, ms2)) a) ∧
  (λn. s1.cc_fp_regs 0 n) =
    (λn. mc_conf.target.get_fp_reg
           (mc_conf.ccache_interfer 0
              (mc_conf.target.get_reg ms2 mc_conf.ptr_reg,
               mc_conf.target.get_reg ms2 mc_conf.len_reg, ms2)) n)
``;
val _ = stmt "oracle_tie_ccache_residues" oracle_tie_ccache_residues_tm;
val _ = stmt_types "oracle_tie_ccache_residues_types" oracle_tie_ccache_residues_tm;
val ffi_entry_pcs_NOT_ccache_OR_halt_pc_tm = ``
   find_index pc mc_conf.ffi_entry_pcs 0 =
      SOME index /\
   mc_conf.halt_pc <> EL index mc_conf.ffi_entry_pcs /\
   mc_conf.ccache_pc <> EL index mc_conf.ffi_entry_pcs ==>
   pc <> mc_conf.ccache_pc /\
   pc <> mc_conf.halt_pc
``;
val _ = stmt "ffi_entry_pcs_NOT_ccache_OR_halt_pc" ffi_entry_pcs_NOT_ccache_OR_halt_pc_tm;
val _ = stmt_types "ffi_entry_pcs_NOT_ccache_OR_halt_pc_types" ffi_entry_pcs_NOT_ccache_OR_halt_pc_tm;
val no_share_mem_lemma_tm = ``
  mmio_pcs_min_index ffi_names = SOME i /\
  asm_fetch_aux pc code = SOME (LabAsm Install c l n) /\
  no_install_or_no_share_mem code ffi_names ==>
  i = LENGTH ffi_names
``;
val _ = stmt "no_share_mem_lemma" no_share_mem_lemma_tm;
val _ = stmt_types "no_share_mem_lemma_types" no_share_mem_lemma_tm;
val EL_get_ffi_index_MEM_tm = ``
   MEM s ls ⇒ EL (get_ffi_index ls s) ls = s
``;
val _ = stmt "EL_get_ffi_index_MEM" EL_get_ffi_index_MEM_tm;
val _ = stmt_types "EL_get_ffi_index_MEM_types" EL_get_ffi_index_MEM_tm;
val ffi_name_NOT_Mapped_tm = ``
  mmio_pcs_min_index ffi_names = SOME i /\ (∃str. s = ExtCall str) ∧
  MEM s ffi_names ==>
  get_ffi_index ffi_names s < i
``;
val _ = stmt "ffi_name_NOT_Mapped" ffi_name_NOT_Mapped_tm;
val _ = stmt_types "ffi_name_NOT_Mapped_types" ffi_name_NOT_Mapped_tm;
val no_share_mem_APPEND_tm = ``
  no_share_mem_inst code /\
  no_share_mem_inst secs ==>
  no_share_mem_inst (code ++ secs)
``;
val _ = stmt "no_share_mem_APPEND" no_share_mem_APPEND_tm;
val _ = stmt_types "no_share_mem_APPEND_types" no_share_mem_APPEND_tm;
val no_install_APPEND_IMP_tm = ``
  no_install (code ++ secs) ==>
  no_install code /\ no_install secs
``;
val _ = stmt "no_install_APPEND_IMP" no_install_APPEND_IMP_tm;
val _ = stmt_types "no_install_APPEND_IMP_types" no_install_APPEND_IMP_tm;
val no_share_mem_IMP_get_shmem_info_tm = ``
!code p ffi_names shmem_info.
  no_share_mem_inst code ==>
  get_shmem_info code p ffi_names shmem_info = (ffi_names,shmem_info)
``;
val _ = stmt "no_share_mem_IMP_get_shmem_info" no_share_mem_IMP_get_shmem_info_tm;
val _ = stmt_types "no_share_mem_IMP_get_shmem_info_types" no_share_mem_IMP_get_shmem_info_tm;
val IMP_ffi_entry_pcs_disjoint_Asm_tm = ``
!(s1:('a,lab_to_target$config,'ffi) labSem$state) (mc_conf: ('a,'state,'b) machine_config).
  code_similar s1.code code2 /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
  asm_fetch_aux s1.pc s1.code = SOME (Asm instr _bytes _len) /\
  (!op re a. instr <> ShareMem op re a) /\
  share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain /\
  bytes_in_mem (p + n2w (pos_val s1.pc 0 code2)) bytes' t1.mem
    t1.mem_domain s1.mem_domain /\
  pos_val (s1.pc + 1) 0 code2 = LENGTH bytes' + pos_val s1.pc 0 code2 /\
  t1.pc = p + n2w (pos_val s1.pc 0 code2)
  ==>
  ffi_entry_pcs_disjoint (mc_conf: ('a, 'state, 'b) machine_config) t1 (LENGTH bytes')
``;
val _ = stmt "IMP_ffi_entry_pcs_disjoint_Asm" IMP_ffi_entry_pcs_disjoint_Asm_tm;
val _ = stmt_types "IMP_ffi_entry_pcs_disjoint_Asm_types" IMP_ffi_entry_pcs_disjoint_Asm_tm;
val IMP_ffi_entry_pcs_disjoint_LabAsm_tm = ``
!(s1:('a,lab_to_target$config,'ffi) labSem$state) (mc_conf: ('a,'state,'b) machine_config).
  code_similar s1.code code2 /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
  asm_fetch_aux s1.pc s1.code = SOME (LabAsm instr _pos _bytes _len) /\
  share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain /\
  bytes_in_mem (p + n2w (pos_val s1.pc 0 code2)) bytes' t1.mem
    t1.mem_domain s1.mem_domain /\
  pos_val (s1.pc + 1) 0 code2 = LENGTH bytes' + pos_val s1.pc 0 code2 /\
  t1.pc = p + n2w (pos_val s1.pc 0 code2)
  ==>
  ffi_entry_pcs_disjoint (mc_conf: ('a, 'state, 'b) machine_config) t1 (LENGTH bytes')
``;
val _ = stmt "IMP_ffi_entry_pcs_disjoint_LabAsm" IMP_ffi_entry_pcs_disjoint_LabAsm_tm;
val _ = stmt_types "IMP_ffi_entry_pcs_disjoint_LabAsm_types" IMP_ffi_entry_pcs_disjoint_LabAsm_tm;
val EVEN_add_AND_tm = ``
   (1w && p) = 0w ∧
  EVEN x ⇒
  (1w && (p + n2w x)) = 0w
``;
val _ = stmt "EVEN_add_AND" EVEN_add_AND_tm;
val _ = stmt_types "EVEN_add_AND_types" EVEN_add_AND_tm;
val word_cmp_lemma_tm = ``
  state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
    (word_cmp cmp (read_reg rr s1) (reg_imm ri s1) = SOME x) ==>
    (x = word_cmp cmp (read_reg rr t1) (reg_imm ri t1))
``;
val _ = stmt "word_cmp_lemma" word_cmp_lemma_tm;
val _ = stmt_types "word_cmp_lemma_types" word_cmp_lemma_tm;
val list_add_if_fresh_thm_tm = ``
   list_add_if_fresh s l =
    if MEM s l then l else l ++ [s]
``;
val _ = stmt "list_add_if_fresh_thm" list_add_if_fresh_thm_tm;
val _ = stmt_types "list_add_if_fresh_thm_types" list_add_if_fresh_thm_tm;
val find_ffi_names_append_tm = ``
  ∀l1 l2.
  find_ffi_names (l1++l2) =
  (find_ffi_names l2) ++
  FILTER (λn. ¬ MEM n (find_ffi_names l2)) (find_ffi_names l1)
``;
val _ = stmt "find_ffi_names_append" find_ffi_names_append_tm;
val _ = stmt_types "find_ffi_names_append_types" find_ffi_names_append_tm;
val loc_to_pc_append_tm = ``
  ∀l1 l2 c1 c2 conf labs ffis pos.
  EVERY sec_labels_ok (c1++c2) ⇒
  loc_to_pc l1 l2 (c1++c2) =
  case loc_to_pc l1 l2 c1 of
    SOME x => SOME x
  | NONE =>
    case loc_to_pc l1 l2 c2 of
      SOME x => SOME (x + SUM (MAP (len_no_lab o Section_lines) c1))
    | NONE => NONE
``;
val _ = stmt "loc_to_pc_append" loc_to_pc_append_tm;
val _ = stmt_types "loc_to_pc_append_types" loc_to_pc_append_tm;
val line_length_MOD_0_tm = ``
  encoder_correct mc_conf.target /\
    (~EVEN p ==> (mc_conf.target.config.code_alignment = 0)) /\
    line_ok mc_conf.target.config labs ffi_names p h ==>
    (line_length h MOD 2 ** mc_conf.target.config.code_alignment = 0)
``;
val _ = stmt "line_length_MOD_0" line_length_MOD_0_tm;
val _ = stmt_types "line_length_MOD_0_types" line_length_MOD_0_tm;
val all_enc_ok_aligned_pos_val_tm = ``
  !(mc_conf : ('a, 'b, 'c) machine_config) labs code2 pc ffi_names.
   all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
   (has_odd_inst code2 ==> mc_conf.target.config.code_alignment = 0) /\
   encoder_correct mc_conf.target ==>
   aligned mc_conf.target.config.code_alignment (n2w (pos_val pc 0 code2):'a word)
``;
val _ = stmt "all_enc_ok_aligned_pos_val" all_enc_ok_aligned_pos_val_tm;
val _ = stmt_types "all_enc_ok_aligned_pos_val_types" all_enc_ok_aligned_pos_val_tm;
val _ = OS.Process.exit OS.Process.success;
