load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble asmPropsTheory lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
(* [local] theorems of lab_to_targetProofScript.sml are not exported; their
   exact unchanged statement text is re-elaborated (with the source's ^s1
   antiquotation expanded to its type annotation) and printed with inferred
   types.  These rows are statement captures, not theorem replays. *)
fun stmt label tm = (print(label ^ "="); print_term tm; print "\n");
fun stmt_types label tm =
 (show_types := true; stmt label tm; show_types := false);
val prog_to_bytes_lemma_tm = ``
  !code2 code1 pc i pos.
      code_similar code1 code2 /\
      all_enc_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names pos code2 /\
      (asm_fetch_aux pc code1 = SOME i) ==>
      ?bs j bs2.
        (prog_to_bytes code2 = bs ++ line_bytes j ++ bs2) /\
        (LENGTH bs + pos = pos_val pc pos code2) /\
        (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc+1) pos code2) /\
        line_similar i j /\
        line_ok mc_conf.target.config labs ffi_names (pos_val pc pos code2) j
``;
val _ = stmt "prog_to_bytes_lemma" prog_to_bytes_lemma_tm;
val _ = stmt_types "prog_to_bytes_lemma_types" prog_to_bytes_lemma_tm;
val IMP_bytes_in_memory_tm = ``
  code_similar code1 code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_mem p (prog_to_bytes code2) m (dm:'a word set) dm1 ==>
    ?j.
      bytes_in_mem (p + n2w (pos_val pc 0 code2)) (line_bytes j) m dm dm1 /\
      line_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names (pos_val pc 0 code2) j /\
      (pos_val (pc+1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j)) /\
      line_similar i j
``;
val _ = stmt "IMP_bytes_in_memory" IMP_bytes_in_memory_tm;
val _ = stmt_types "IMP_bytes_in_memory_types" IMP_bytes_in_memory_tm;
val IMP_bytes_in_memory_JumpReg_tm = ``
  code_similar s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.target.config.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_JumpReg" IMP_bytes_in_memory_JumpReg_tm;
val _ = stmt_types "IMP_bytes_in_memory_JumpReg_types" IMP_bytes_in_memory_JumpReg_tm;
val IMP_bytes_in_memory_Jump_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_Jump" IMP_bytes_in_memory_Jump_tm;
val _ = stmt_types "IMP_bytes_in_memory_Jump_types" IMP_bytes_in_memory_Jump_tm;
val IMP_bytes_in_memory_JumpCmp_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (JumpCmp cmp rr ri tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_JumpCmp" IMP_bytes_in_memory_JumpCmp_tm;
val _ = stmt_types "IMP_bytes_in_memory_JumpCmp_types" IMP_bytes_in_memory_JumpCmp_tm;
val IMP_bytes_in_memory_JumpCmp_1_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (JumpCmp cmp rr ri tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_JumpCmp_1" IMP_bytes_in_memory_JumpCmp_1_tm;
val _ = stmt_types "IMP_bytes_in_memory_JumpCmp_1_types" IMP_bytes_in_memory_JumpCmp_1_tm;
val IMP_bytes_in_memory_Call_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok
      (mc_conf: ('a,'state,'b) machine_config).target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem
      (t1:'a asm_state).mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n)) ==>
    F
``;
val _ = stmt "IMP_bytes_in_memory_Call" IMP_bytes_in_memory_Call_tm;
val _ = stmt_types "IMP_bytes_in_memory_Call_types" IMP_bytes_in_memory_Call_tm;
val IMP_bytes_in_memory_LocValue_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos (Lab l1 l2) labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (Loc reg tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Loc reg tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_LocValue" IMP_bytes_in_memory_LocValue_tm;
val _ = stmt_types "IMP_bytes_in_memory_LocValue_types" IMP_bytes_in_memory_LocValue_tm;
val IMP_bytes_in_memory_Inst_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi(Inst i)) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.config.encode (Inst i) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst i) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_Inst" IMP_bytes_in_memory_Inst_tm;
val _ = stmt_types "IMP_bytes_in_memory_Inst_types" IMP_bytes_in_memory_Inst_tm;
val IMP_bytes_in_memory_Cbw_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Cbw r1 r2) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.config.encode (Inst (Mem Store8 r2 (Addr r1 0w))) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst (Mem Store8 r2 (Addr r1 0w))) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_Cbw" IMP_bytes_in_memory_Cbw_tm;
val _ = stmt_types "IMP_bytes_in_memory_Cbw_types" IMP_bytes_in_memory_Cbw_tm;
val IMP_bytes_in_memory_CallFFI_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (CallFFI name) l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + (3 + get_ffi_index ffi_names (ExtCall name)) * ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_CallFFI" IMP_bytes_in_memory_CallFFI_tm;
val _ = stmt_types "IMP_bytes_in_memory_CallFFI_types" IMP_bytes_in_memory_CallFFI_tm;
val IMP_bytes_in_memory_Halt_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Halt l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_Halt" IMP_bytes_in_memory_Halt_tm;
val _ = stmt_types "IMP_bytes_in_memory_Halt_types" IMP_bytes_in_memory_Halt_tm;
val IMP_bytes_in_memory_Install_tm = ``
  code_similar (s1:('a,lab_to_target$config,'ffi) labSem$state).code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Install c l n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + 2 * ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
``;
val _ = stmt "IMP_bytes_in_memory_Install" IMP_bytes_in_memory_Install_tm;
val _ = stmt_types "IMP_bytes_in_memory_Install_types" IMP_bytes_in_memory_Install_tm;
val bytes_in_mem_IMP_memory_tm = ``
  !xs a.
      (!a. ~(a IN dm1) ==> m a = m1 a) ==>
      bytes_in_mem a xs m dm dm1 ==>
      bytes_in_memory a xs m1 dm
``;
val _ = stmt "bytes_in_mem_IMP_memory" bytes_in_mem_IMP_memory_tm;
val _ = stmt_types "bytes_in_mem_IMP_memory_types" bytes_in_mem_IMP_memory_tm;
val _ = emit "asm_fetch_aux_pos_val_LENGTH_EQ" asm_fetch_aux_pos_val_LENGTH_EQ;
val _ = emit_types "asm_fetch_aux_pos_val_LENGTH_EQ_types" asm_fetch_aux_pos_val_LENGTH_EQ;
val _ = emit "IMP_bytes_in_memory_ShareMem" IMP_bytes_in_memory_ShareMem;
val _ = emit_types "IMP_bytes_in_memory_ShareMem_types" IMP_bytes_in_memory_ShareMem;
val _ = OS.Process.exit OS.Process.success;
