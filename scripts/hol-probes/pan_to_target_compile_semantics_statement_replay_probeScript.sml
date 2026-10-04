(* Literal source replay of the statement of pan_to_targetProof pan_to_target_compile_semantics
   (1257-1300) for a typed capture. backendProofTheory and pan_to_targetProofTheory are unbuilt;
   their definitions used by the statement are replayed literally (guarded against the source) over
   the loaded original theories. The statement is parsed and printed with types; it is not proved
   here and this is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "backendTheory"; load "stack_removeProofTheory"; load "stack_namesTheory";
load "stackPropsTheory"; load "data_to_wordTheory"; load "lab_to_targetTheory"; load "lab_to_targetProofTheory";
load "targetSemTheory"; load "alignmentTheory"; load "pan_to_targetTheory"; load "word_depthTheory";
load "pan_to_wordProofTheory"; load "panSemTheory"; load "panPropsTheory"; load "semanticsPropsTheory"; load "set_sepTheory";
open HolKernel Parse bossLib preamble backendTheory stack_namesTheory stackPropsTheory alignmentTheory targetSemTheory set_sepTheory;
val _ = Globals.linewidth := 1000000;
fun read_source rel = let val cake = case OS.Process.getEnv "CAKEML" of SOME p => p | NONE => raise Fail "CAKEML is required"
  val st = TextIO.openIn (OS.Path.concat (cake, rel)) val t = TextIO.inputAll st in TextIO.closeIn st; t end;
val backend_src = read_source "compiler/backend/proofs/backendProofScript.sml";
val target_src = read_source "pancake/proofs/pan_to_targetProofScript.sml";
fun guard name src lit = if String.isSubstring lit src then () else raise Fail (name ^ " literal source changed");
val _ = guard "Definition backend_config_ok_def:" backend_src "Definition backend_config_ok_def:\n  backend_config_ok (asm_conf:'a asm_config) (c:config) \226\135\148\n    c.source_conf = prim_src_config \226\136\167\n    0 < c.clos_conf.max_app \226\136\167\n    c.bvl_conf.next_name2 = bvl_num_stubs + 2 \226\136\167\n    LENGTH asm_conf.avoid_regs + 13 \226\137\164 asm_conf.reg_count \226\136\167\n    c.lab_conf.pos = 0 \226\136\167\n    c.lab_conf.labels = LN \226\136\167\n    conf_ok (:'a) c.data_conf \226\136\167\n    (c.data_conf.has_longdiv \226\135\146 asm_conf.ISA = x86_64) /\\\n    (c.data_conf.has_div \226\135\146\n      asm_conf.ISA = ARMv8 \226\136\168 asm_conf.ISA = MIPS \226\136\168\n      asm_conf.ISA = RISC_V) \226\136\167\n    (c.data_conf.has_fp_tern \226\135\148\n        asm_conf.ISA = ARMv7 \226\136\167 2 < asm_conf.fp_reg_count) \226\136\167\n    (c.data_conf.has_fp_ops \226\135\148 1 < asm_conf.fp_reg_count) \226\136\167\n    max_stack_alloc \226\137\164 2 * max_heap_limit (:'a) c.data_conf \226\136\146 1 \226\136\167\n    c.stack_conf.perf_calls = F \226\136\167\n    addr_offset_ok asm_conf 0w \226\136\167\n    hw_offset_ok asm_conf 0w \226\136\167\n    (\226\136\128w. -8w \226\137\164 w \226\136\167 w \226\137\164 8w \226\135\146 byte_offset_ok asm_conf w) \226\136\167\n    asm_conf.valid_imm (INL Add) 8w \226\136\167\n    asm_conf.valid_imm (INL Add) 4w \226\136\167\n    asm_conf.valid_imm (INL Add) 1w \226\136\167\n    asm_conf.valid_imm (INL Sub) 1w \226\136\167\n    OPTION_ALL (EVERY (\206\187x. \226\136\131s. x = ExtCall s)) c.lab_conf.ffi_names \226\136\167\n    find_name c.stack_conf.reg_names PERMUTES UNIV \226\136\167\n    names_ok c.stack_conf.reg_names asm_conf.reg_count asm_conf.avoid_regs \226\136\167\n    stackProps$fixed_names c.stack_conf.reg_names asm_conf \226\136\167\n    (\226\136\128s. addr_offset_ok asm_conf (store_offset s)) \226\136\167\n    (\226\136\128s. hw_offset_ok asm_conf (store_offset s)) \226\136\167\n    (\226\136\128n.\n         n \226\137\164 max_stack_alloc \226\135\146\n         asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:\206\177) DIV 8))) \226\136\167\n         asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:\206\177) DIV 8))))\nEnd";
val _ = guard "Definition mc_init_ok_def:" backend_src "Definition mc_init_ok_def:\n  mc_init_ok asm_conf c mc \226\135\148\n  EVERY (\206\187r. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] \226\136\167\n  find_name c.stack_conf.reg_names 4 = mc.len2_reg \226\136\167\n  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg \226\136\167\n  find_name c.stack_conf.reg_names 2 = mc.len_reg \226\136\167\n  find_name c.stack_conf.reg_names 1 = mc.ptr_reg \226\136\167\n  find_name c.stack_conf.reg_names 0 =\n    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\136\167\n  c.data_conf.be = mc.target.config.big_endian \226\136\167\n  (* the next four are implied by injectivity of find_name *)\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.len2_reg \226\136\167\n  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) \226\137\160 mc.ptr2_reg \226\136\167\n  \194\172MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs \226\136\167\n   asm_conf = mc.target.config\nEnd";
val _ = guard "Definition heap_regs_def:" backend_src "Definition heap_regs_def:\n  heap_regs reg_names =\n    (find_name reg_names 2, find_name reg_names 4)\nEnd";
val _ = guard "Definition read_limits_def:" backend_src "Definition read_limits_def:\n  read_limits (asm_conf:'a asm_config) (c:config) mc ms =\n    stack_removeProof$get_stack_heap_limit\n      (2 * max_heap_limit (:\206\177) c.data_conf - 1)\n      (mc.target.get_reg ms (find_name c.stack_conf.reg_names 2) :'a word,\n       mc.target.get_reg ms (find_name c.stack_conf.reg_names 3) :'a word,\n       mc.target.get_reg ms (find_name c.stack_conf.reg_names 4) :'a word)\nEnd";
val _ = guard "Definition pancake_good_code_def:" target_src "Definition pancake_good_code_def:\n  pancake_good_code pan_code = EVERY good_panops pan_code\nEnd";
val _ = guard "Definition pan_installed_def:" target_src "Definition pan_installed_def:\n  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms p_mem p_dom sdm' \226\135\148\n  \226\136\131t m bitmap_ptr bitmaps_dm sdm.\n  let heap_stack_dm = { w | t.regs r1 <=+ w \226\136\167 w <+ t.regs r2 } in\n    (\226\136\128a. a \226\136\136 p_dom \226\135\146 m a = p_mem a) \226\136\167\n    good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm \226\136\170 bitmaps_dm) sdm \226\136\167 sdm' = sdm \226\136\169 byte_aligned \226\136\167\n    byte_aligned (t.regs r1) /\\\n\n    byte_aligned (t.regs r2) /\\\n    byte_aligned bitmap_ptr /\\\n    t.regs r1 \226\137\164\226\130\138 t.regs r2 /\\\n    1024w * bytes_in_word \226\137\164\226\130\138 t.regs r2 - t.regs r1 /\\\n    DISJOINT heap_stack_dm bitmaps_dm \226\136\167\n    m (t.regs r1) = Word bitmap_ptr \226\136\167\n    m (t.regs r1 + bytes_in_word) =\n    Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) \226\136\167\n    m (t.regs r1 + 2w * bytes_in_word) =\n    Word (bitmap_ptr + bytes_in_word * n2w data_sp +\n          bytes_in_word * n2w (LENGTH bitmaps)) \226\136\167\n    m (t.regs r1 + 3w * bytes_in_word) =\n    Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) \226\136\167\n    m (t.regs r1 + 4w * bytes_in_word) =\n    Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) \226\136\167\n    (word_list bitmap_ptr (MAP Word bitmaps) *\n     word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)\n    (fun2set (m,byte_aligned \226\136\169 bitmaps_dm)) \226\136\167\n    ffi_names = SOME mc_conf.ffi_names \226\136\167\n    (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>\n         MAP (\\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) shmem_extra =\n         DROP i (MAP w2n mc_conf.ffi_entry_pcs) \226\136\167\n         mc_conf.mmio_info =\n         ZIP (GENLIST (\206\187index. index + i) (LENGTH shmem_extra),\n             (MAP (\206\187rec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off), rec.reg,\n                        n2w rec.exit_pc + mc_conf.target.get_pc ms))\n                                                           shmem_extra)) \226\136\167\n    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))\nEnd";
val _ = guard "Definition compile_prog_max_def:" target_src "Definition compile_prog_max_def:\n  compile_prog_max c mc prog =\n    let asm_conf = mc.target.config in\n    let prog = pan_to_word$compile_prog asm_conf.ISA prog in\n    let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in\n    let (bm,c',fs,p) = word_to_stack$compile asm_conf F wprog in\n    let max = max_depth c'.stack_frame_size (full_call_graph InitGlobals_location (fromAList wprog)) in\n      (from_stack asm_conf c LN p bm, max)\nEnd";
val _ = guard "Definition option_lt_def[simp]:" target_src "Definition option_lt_def[simp]:\n  (option_lt n0 NONE \226\135\148 T) \226\136\167 (option_lt NONE (SOME n1) \226\135\148 F) \226\136\167\n  (option_lt (SOME n1) (SOME n2) \226\135\148 n1 < n2:num)\nEnd";
val _ = guard "pan_to_target_compile_semantics" target_src "Theorem pan_to_target_compile_semantics:\n  compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) \226\136\167\n  pancake_good_code pan_code \226\136\167\n  distinct_params (functions pan_code) \226\136\167\n  ALL_DISTINCT (MAP FST(functions pan_code)) \226\136\167\n  s.code = FEMPTY \226\136\167\n  s.locals = FEMPTY \226\136\167\n  s.globals = FEMPTY \226\136\167\n  size_of_eids pan_code < dimword (:\206\177) \226\136\167\n  s.eshapes = FEMPTY \226\136\167\n  backend_config_ok mc.target.config c \226\136\167 lab_to_targetProof$mc_conf_ok mc \226\136\167\n  mc_init_ok mc.target.config c mc \226\136\167 mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  0w <\226\130\138 mc.target.get_reg ms mc.len_reg \226\136\167\n  globals_size = (let dec_shs = dec_shapes pan_code;\n    struct_ctxt = panSem$decs_stcnames [] pan_code\n  in SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) \226\136\167\n  mc.target.get_reg ms mc.len_reg  <\226\130\138 mc.target.get_reg ms mc.ptr2_reg \226\136\167\n  mc.target.get_reg ms mc.len_reg = s.base_addr \226\136\167\n  globals_allocatable s pan_code \226\136\167\n  heap_len = w2n ((mc.target.get_reg ms mc.ptr2_reg) + -1w * s.base_addr) DIV (dimindex (:\206\177) DIV 8) \226\136\167\n  s.top_addr = s.base_addr + bytes_in_word * n2w heap_len - n2w(globals_size*dimindex (:\206\177) DIV 8) \226\136\167\n  globals_size \226\137\164 heap_len \226\136\167\n  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len-globals_size) \226\136\167\n  aligned (shift (:'a) + 1) ((mc.target.get_reg ms mc.ptr2_reg) + -1w * (mc.target.get_reg ms mc.len_reg)) \226\136\167\n  adj_ptr2 = (mc.target.get_reg ms mc.len_reg) + bytes_in_word * n2w max_stack_alloc \226\136\167\n  adj_ptr4 = (mc.target.get_reg ms mc.len2_reg) - bytes_in_word * n2w max_stack_alloc \226\136\167\n  adj_ptr2 \226\137\164\226\130\138 (mc.target.get_reg ms mc.ptr2_reg) \226\136\167\n  (mc.target.get_reg ms mc.ptr2_reg) \226\137\164\226\130\138 adj_ptr4 \226\136\167\n  w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * (mc.target.get_reg ms mc.len_reg)) \226\137\164\n  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) \226\136\167\n  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) < dimword (:'a) \226\136\167\n  s.ffi = ffi \226\136\167 mc.target.config.big_endian = s.be \226\136\167\n  OPTION_ALL (EVERY $ \\x. \226\136\131s. x = ExtCall s) c.lab_conf.ffi_names \226\136\167\n  pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names\n                (heap_regs c.stack_conf.reg_names) mc\n                c'.lab_conf.shmem_extra ms\n                (wlab_wloc o s.memory)\n                s.memaddrs s.sh_memaddrs \226\136\167\n  start = \194\171main\194\187 \226\136\167\n  semantics_decls s start pan_code \226\137\160 Fail \226\135\146\n  machine_sem (mc:(\206\177,\206\178,\206\179) machine_config) (ffi:'ffi ffi_state) ms \226\138\134\n              extend_with_resource_limit'\n              (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))\n              {semantics_decls (s:('a,'ffi) panSem$state) start pan_code}";
val _ = new_theory "flapjack_pan_to_target_compile_semantics_statement_replay";
Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``
Overload word_to_word_compile[local] = ``word_to_word$compile``
Overload word_to_stack_compile[local] = ``word_to_stack$compile``
Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog``
Definition backend_config_ok_def:
  backend_config_ok (asm_conf:'a asm_config) (c:config) ⇔
    c.source_conf = prim_src_config ∧
    0 < c.clos_conf.max_app ∧
    c.bvl_conf.next_name2 = bvl_num_stubs + 2 ∧
    LENGTH asm_conf.avoid_regs + 13 ≤ asm_conf.reg_count ∧
    c.lab_conf.pos = 0 ∧
    c.lab_conf.labels = LN ∧
    conf_ok (:'a) c.data_conf ∧
    (c.data_conf.has_longdiv ⇒ asm_conf.ISA = x86_64) /\
    (c.data_conf.has_div ⇒
      asm_conf.ISA = ARMv8 ∨ asm_conf.ISA = MIPS ∨
      asm_conf.ISA = RISC_V) ∧
    (c.data_conf.has_fp_tern ⇔
        asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count) ∧
    (c.data_conf.has_fp_ops ⇔ 1 < asm_conf.fp_reg_count) ∧
    max_stack_alloc ≤ 2 * max_heap_limit (:'a) c.data_conf − 1 ∧
    c.stack_conf.perf_calls = F ∧
    addr_offset_ok asm_conf 0w ∧
    hw_offset_ok asm_conf 0w ∧
    (∀w. -8w ≤ w ∧ w ≤ 8w ⇒ byte_offset_ok asm_conf w) ∧
    asm_conf.valid_imm (INL Add) 8w ∧
    asm_conf.valid_imm (INL Add) 4w ∧
    asm_conf.valid_imm (INL Add) 1w ∧
    asm_conf.valid_imm (INL Sub) 1w ∧
    OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
    find_name c.stack_conf.reg_names PERMUTES UNIV ∧
    names_ok c.stack_conf.reg_names asm_conf.reg_count asm_conf.avoid_regs ∧
    stackProps$fixed_names c.stack_conf.reg_names asm_conf ∧
    (∀s. addr_offset_ok asm_conf (store_offset s)) ∧
    (∀s. hw_offset_ok asm_conf (store_offset s)) ∧
    (∀n.
         n ≤ max_stack_alloc ⇒
         asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:α) DIV 8))) ∧
         asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:α) DIV 8))))
End
Definition mc_init_ok_def:
  mc_init_ok asm_conf c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 4 = mc.len2_reg ∧
  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  c.data_conf.be = mc.target.config.big_endian ∧
  (* the next four are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len2_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr2_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs ∧
   asm_conf = mc.target.config
End
Definition heap_regs_def:
  heap_regs reg_names =
    (find_name reg_names 2, find_name reg_names 4)
End
Definition read_limits_def:
  read_limits (asm_conf:'a asm_config) (c:config) mc ms =
    stack_removeProof$get_stack_heap_limit
      (2 * max_heap_limit (:α) c.data_conf - 1)
      (mc.target.get_reg ms (find_name c.stack_conf.reg_names 2) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 3) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 4) :'a word)
End
Definition pancake_good_code_def:
  pancake_good_code pan_code = EVERY good_panops pan_code
End
Definition pan_installed_def:
  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms p_mem p_dom sdm' ⇔
  ∃t m bitmap_ptr bitmaps_dm sdm.
  let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
    (∀a. a ∈ p_dom ⇒ m a = p_mem a) ∧
    good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) sdm ∧ sdm' = sdm ∩ byte_aligned ∧
    byte_aligned (t.regs r1) /\

    byte_aligned (t.regs r2) /\
    byte_aligned bitmap_ptr /\
    t.regs r1 ≤₊ t.regs r2 /\
    1024w * bytes_in_word ≤₊ t.regs r2 - t.regs r1 /\
    DISJOINT heap_stack_dm bitmaps_dm ∧
    m (t.regs r1) = Word bitmap_ptr ∧
    m (t.regs r1 + bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 2w * bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w data_sp +
          bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 3w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
    m (t.regs r1 + 4w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
    (word_list bitmap_ptr (MAP Word bitmaps) *
     word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
    (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
    ffi_names = SOME mc_conf.ffi_names ∧
    (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>
         MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) shmem_extra =
         DROP i (MAP w2n mc_conf.ffi_entry_pcs) ∧
         mc_conf.mmio_info =
         ZIP (GENLIST (λindex. index + i) (LENGTH shmem_extra),
             (MAP (λrec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off), rec.reg,
                        n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                                           shmem_extra)) ∧
    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))
End
Definition compile_prog_max_def:
  compile_prog_max c mc prog =
    let asm_conf = mc.target.config in
    let prog = pan_to_word$compile_prog asm_conf.ISA prog in
    let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in
    let (bm,c',fs,p) = word_to_stack$compile asm_conf F wprog in
    let max = max_depth c'.stack_frame_size (full_call_graph InitGlobals_location (fromAList wprog)) in
      (from_stack asm_conf c LN p bm, max)
End
Definition option_lt_def[simp]:
  (option_lt n0 NONE ⇔ T) ∧ (option_lt NONE (SOME n1) ⇔ F) ∧
  (option_lt (SOME n1) (SOME n2) ⇔ n1 < n2:num)
End
val stmt = Parse.Term [QUOTE "  compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) \226\136\167\n  pancake_good_code pan_code \226\136\167\n  distinct_params (functions pan_code) \226\136\167\n  ALL_DISTINCT (MAP FST(functions pan_code)) \226\136\167\n  s.code = FEMPTY \226\136\167\n  s.locals = FEMPTY \226\136\167\n  s.globals = FEMPTY \226\136\167\n  size_of_eids pan_code < dimword (:\206\177) \226\136\167\n  s.eshapes = FEMPTY \226\136\167\n  backend_config_ok mc.target.config c \226\136\167 lab_to_targetProof$mc_conf_ok mc \226\136\167\n  mc_init_ok mc.target.config c mc \226\136\167 mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  0w <\226\130\138 mc.target.get_reg ms mc.len_reg \226\136\167\n  globals_size = (let dec_shs = dec_shapes pan_code;\n    struct_ctxt = panSem$decs_stcnames [] pan_code\n  in SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) \226\136\167\n  mc.target.get_reg ms mc.len_reg  <\226\130\138 mc.target.get_reg ms mc.ptr2_reg \226\136\167\n  mc.target.get_reg ms mc.len_reg = s.base_addr \226\136\167\n  globals_allocatable s pan_code \226\136\167\n  heap_len = w2n ((mc.target.get_reg ms mc.ptr2_reg) + -1w * s.base_addr) DIV (dimindex (:\206\177) DIV 8) \226\136\167\n  s.top_addr = s.base_addr + bytes_in_word * n2w heap_len - n2w(globals_size*dimindex (:\206\177) DIV 8) \226\136\167\n  globals_size \226\137\164 heap_len \226\136\167\n  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len-globals_size) \226\136\167\n  aligned (shift (:'a) + 1) ((mc.target.get_reg ms mc.ptr2_reg) + -1w * (mc.target.get_reg ms mc.len_reg)) \226\136\167\n  adj_ptr2 = (mc.target.get_reg ms mc.len_reg) + bytes_in_word * n2w max_stack_alloc \226\136\167\n  adj_ptr4 = (mc.target.get_reg ms mc.len2_reg) - bytes_in_word * n2w max_stack_alloc \226\136\167\n  adj_ptr2 \226\137\164\226\130\138 (mc.target.get_reg ms mc.ptr2_reg) \226\136\167\n  (mc.target.get_reg ms mc.ptr2_reg) \226\137\164\226\130\138 adj_ptr4 \226\136\167\n  w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * (mc.target.get_reg ms mc.len_reg)) \226\137\164\n  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) \226\136\167\n  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) < dimword (:'a) \226\136\167\n  s.ffi = ffi \226\136\167 mc.target.config.big_endian = s.be \226\136\167\n  OPTION_ALL (EVERY $ \\x. \226\136\131s. x = ExtCall s) c.lab_conf.ffi_names \226\136\167\n  pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names\n                (heap_regs c.stack_conf.reg_names) mc\n                c'.lab_conf.shmem_extra ms\n                (wlab_wloc o s.memory)\n                s.memaddrs s.sh_memaddrs \226\136\167\n  start = \194\171main\194\187 \226\136\167\n  semantics_decls s start pan_code \226\137\160 Fail \226\135\146\n  machine_sem (mc:(\206\177,\206\178,\206\179) machine_config) (ffi:'ffi ffi_state) ms \226\138\134\n              extend_with_resource_limit'\n              (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))\n              {semantics_decls (s:('a,'ffi) panSem$state) start pan_code}"];
val _ = (print "pan_to_target_compile_semantics_statement="; print_term stmt; print "\n");
val _ = (print "pan_to_target_compile_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term stmt; print "\n");
val _ = (print "pan_to_target_compile_semantics_free_vars="; print (String.concatWith " " (map (fn v => fst (dest_var v)) (Term.free_vars_lr stmt))); print "\n");
load "byteTheory";
val _ = (print "bytes_in_word_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl byteTheory.bytes_in_word_def); print "\n");
