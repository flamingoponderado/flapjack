load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t=DB.fetch "lab_to_targetProof" "asm_fetch_NOT_ffi_entry_pcs";
val _=capture "asm_fetch_NOT_ffi_entry_pcs" t;
val _=types "asm_fetch_NOT_ffi_entry_pcs_types" t;
val _=print("asm_fetch_NOT_ffi_entry_pcs_hypotheses="^Int.toString(length(hyp t))^"\n");
val _=show_types:=false;
val template = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (-128w,127w); hw_offset := (-128w,127w); byte_offset := (-128w,127w);
 jump_offset := (-128w,127w); cjump_offset := (-128w,127w); loc_offset := (-128w,127w)
 |> : 8 asm_config``;
val cfg = ``^template with <|code_alignment:=1;encode:=(λa.[0w;0w])|>``;
val guest=``ExtCall(strlit "guest")``;
val code=``[Section 1 [Asm (Asmi(Inst Skip)) [0w;0w] 2;Asm (Asmi(Inst Skip)) [0w;0w] 2]]:8 sec list``;
val raw=``mc0:(8,unit,unit) machine_config``;
fun checked label th=(print(label^"=");print_term(rhs(concl(EQT_INTRO th)));print"\n");
fun discharge th=MP th (prove(fst(dest_imp(concl th)),simp [] >> EVAL_TAC >> simp []));
val hmmio=SIMP_RULE(srw_ss())[] (discharge(INST[``ffis:ffiname list``|->``[^guest]``,``l:ffiname list``|->``[]:ffiname list``] mmio_pcs_min_index_APPEND_thm));
val st=``(t0:8 asm_state) with mem := (K (0w:word8))``;
val source=INST_TYPE [``:'a`` |-> ``:8``,``:'state`` |-> ``:unit``,``:'b`` |-> ``:unit``] t;
fun instanceCase label base pos a =
 let val target=``^raw.target with <|config:=^cfg;get_pc:=(K ^base)|>``
     val mc=``^raw with <|target:=^target;ffi_names:=[^guest];ffi_entry_pcs:=[-48w+^base];prog_addresses:={^base;^base+1w;^base+2w;^base+3w};shared_addresses:={};halt_pc:=100w;ccache_pc:=101w|>``
     val instance=INST [mk_var("mc_conf",type_of mc)|->mc,mk_var("code2",type_of code)|->code,mk_var("t",type_of st)|->st,``a:num``|->a,``line:8 line``|->``Asm (Asmi(Inst Skip)) [0w;0w] 2:8 line``,``pos:num``|->pos,``dm:8 word->bool``|->``{}:8 word set``,``ms:unit``|->``():unit``,``ffi_names:ffiname list``|->``[]:ffiname list``,``labs:num num_map num_map``|->``LN:num num_map num_map``,``i:num``|->``1:num``] source
     val guardProof=prove(fst(dest_imp(concl instance)),simp[hmmio] >> EVAL_TAC >> simp [])
 in checked label (MP instance guardProof) end;
val _=instanceCase "first" ``255w:8 word`` ``0:num`` ``0:num``;
val _=instanceCase "wrap" ``255w:8 word`` ``0:num`` ``1:num``;
val _=instanceCase "next" ``255w:8 word`` ``1:num`` ``0:num``;
val _=instanceCase "next_last" ``255w:8 word`` ``1:num`` ``1:num``;
val _=instanceCase "shift_wrap" ``254w:8 word`` ``1:num`` ``1:num``;
val _=instanceCase "shift" ``7w:8 word`` ``0:num`` ``0:num``;
val _=instanceCase "shift_next" ``7w:8 word`` ``1:num`` ``1:num``;
fun observe label q=checked label (prove(q,simp [] >> EVAL_TAC >> simp []));
val _=observe "byte_bound_guard" ``~(2 < LENGTH (line_bytes (Asm (Asmi(Inst Skip)) [0w;0w] 2:8 line)))``;
val _=observe "fetch_guard" ``asm_fetch_aux 2 ^code = NONE``;
