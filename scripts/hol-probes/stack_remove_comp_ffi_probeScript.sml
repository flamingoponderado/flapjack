load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory set_sepTheory wordSemTheory;
val _ = Globals.linewidth := 20000;
val memory_fun2set_IMP_read = prove(``(memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
    a IN d1 /\ m1 a = m a``,
  simp [Once STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS]);
val state_rel_read = prove(``state_rel jump off k s t /\ a IN s.mdomain ==>
    a IN t.mdomain /\ (t.memory a = s.memory a)``,
  full_simp_tac(srw_ss())[state_rel_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC] \\ metis_tac [memory_fun2set_IMP_read]);
val mem_load_byte_aux_IMP = prove(``state_rel jump off k s t /\
    mem_load_byte_aux s.memory s.mdomain s.be a = SOME x ==>
    mem_load_byte_aux t.memory t.mdomain t.be a = SOME x``,
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val read_bytearray_IMP_read_bytearray = prove(``!n a k s t x.
      state_rel jump off k s t /\
      read_bytearray a n (mem_load_byte_aux s.memory s.mdomain s.be) = SOME x ==>
      read_bytearray a n (mem_load_byte_aux t.memory t.mdomain t.be) = SOME x``,
  Induct \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac mem_load_byte_aux_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory miscTheory wordSemTheory set_sepTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [byteTheory.set_byte_bit_field_insert,arithmeticTheory.MOD_0];
fun theoremRow label th = let val th=GEN_ALL th in if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem"; print(label ^ "="); print_thm th; print "\n" end;
fun tree t = if numSyntax.is_numeral t then Arbnum.toString(numSyntax.dest_numeral t) else let val (h,args)=strip_comb t; val {Thy,Name,...}=dest_thy_const h in "(" ^ Thy ^ "$" ^ Name ^ String.concat(map (fn a => " " ^ tree a) args) ^ ")" end;
fun residualRow label q = (print (label ^ "="); print_term(rhs(concl(EVAL q))); print "\n");
fun out label q = let val th=EVAL q; val t=rhs(concl th) in if null(hyp th) andalso null(free_vars t) then () else raise Fail "non-ground observation"; print(label ^ "=" ^ tree t ^ "\n") end;
val write_bytearray_IGNORE_non_aligned = prove(``!new_bytes a.
      (!x. b <> byte_align x) ==>
      write_bytearray a new_bytes m d be b = m b``,   Induct \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]);
val write_bytearray_IGNORE = prove(``!new_bytes a x xx.
      d1 SUBSET d /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x /\ xx ∉ d1 ==>
      write_bytearray a new_bytes m d be xx = m xx``,   Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ rpt gen_tac \\ every_case_tac
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);
val write_bytearray_EQ = prove(``!new_bytes a m1 m y x.
      d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME y /\ m1 x = m x ==>
      write_bytearray a new_bytes m1 d1 be x =
      write_bytearray a new_bytes m d be x``,   Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ rpt gen_tac \\ ntac 2 BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ Cases_on `m1 (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ `byte_align a IN d` by full_simp_tac(srw_ss())[SUBSET_DEF] \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xx ==> yy` mp_tac \\ impl_tac THEN1 (metis_tac [])
  \\ srw_tac[][]
  \\ `write_bytearray (a + 1w) new_bytes m1 d1 be (byte_align a) =
      write_bytearray (a + 1w) new_bytes m d be (byte_align a)` by
    (first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][]);

val write_bytearray_EQ = GEN_ALL write_bytearray_EQ;
val write_bytearray_IGNORE = GEN_ALL write_bytearray_IGNORE;
val write_bytearray_lemma = prove(``  !new_bytes a m1 d1 be x p m d.
      (memory m1 d1 * p) (fun2set (m,d)) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x ==>
      (memory (write_bytearray a new_bytes m1 d1 be) d1 * p)
        (fun2set (write_bytearray a new_bytes m d be,d))``,
  simp [STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS] \\ srw_tac[][]
  \\ `d1 SUBSET d` by full_simp_tac(srw_ss())[SUBSET_DEF]
  THEN1 (res_tac \\ full_simp_tac(srw_ss())[] \\ imp_res_tac write_bytearray_EQ \\ full_simp_tac(srw_ss())[])
  \\ qpat_x_assum `p xx` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x=y)==>x==>y``) \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[EXTENSION] \\ srw_tac[][] \\ EQ_TAC \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `xx IN d`
  \\ Cases_on `xx IN d1` \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_IGNORE \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_EQ \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ metis_tac []);
val _ = Globals.linewidth := 1000000;
open stackSemTheory stack_removeTheory stackPropsTheory;
val state_rel_get_var = GEN_ALL (prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
full_simp_tac(srw_ss())[state_rel_def,get_var_def]));
val cc_ffi = prove(``!name ptr len ptr2 len2 ret s r s2 t1 k off jump.
 evaluate (FFI name ptr len ptr2 len2 ret,s) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k s t1 /\ reg_bound (FFI name ptr len ptr2 len2 ret) k ==>
 ?ck t2. evaluate (comp jump off k (FFI name ptr len ptr2 len2 ret),t1 with clock := ck + t1.clock) = (r,t2) /\
 (case r of SOME (Halt _) => t2.ffi = s2.ffi
 | SOME TimeOut => t2.ffi = s2.ffi
 | SOME (FinalFFI _) => t2.ffi = s2.ffi
 | _ => state_rel jump off k s2 t2)``,
 rpt strip_tac >>
simp [Once comp_def]
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `xxx = (r,s2)` mp_tac
    \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac read_bytearray_IMP_read_bytearray \\ full_simp_tac(srw_ss())[]
    \\ pop_assum kall_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ full_simp_tac(srw_ss())[]
    \\ `t1.ffi = s.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DRESTRICT]
    \\ rev_full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ fs[GSYM STAR_ASSOC]
    \\ match_mp_tac write_bytearray_lemma \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac call_FFI_LENGTH \\ full_simp_tac(srw_ss())[]);
val _ = if null(hyp cc_ffi) andalso null(free_vars(concl cc_ffi)) then () else raise Fail "open theorem";
val _ = print("cc_ffi_statement=" ^ term_to_string(concl cc_ffi) ^ "\n");
val _ = print("cc_ffi_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_ffi))) ^ "\n");
