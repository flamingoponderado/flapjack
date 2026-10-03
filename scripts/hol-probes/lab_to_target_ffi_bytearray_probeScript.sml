load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble labSemTheory lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
(* Statements of the CallFFI bytearray and I/O-name helpers.  has_io_name_def
   is exported and emitted directly; the [local] theorems are re-elaborated
   from the unchanged source text (^s1/^t1 expanded to their type
   annotations); these are statement captures, not theorem replays. *)
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
fun stmt label tm = (print(label ^ "="); print_term tm; print "\n");
fun stmt_types label tm =
 (show_types := true; stmt label tm; show_types := false);
val _ = emit "has_io_name_def" has_io_name_def;
val _ = emit_types "has_io_name_def_types" has_io_name_def;
val read_bytearray_state_rel_tm = ``
  !n a x.
      state_rel (mc_conf,code2,labs,p) (s1:('a,lab_to_target$config,'ffi) labSem$state) t1 ms1 /\
      (read_bytearray a n (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)``;
val _ = stmt "read_bytearray_state_rel" read_bytearray_state_rel_tm;
val _ = stmt_types "read_bytearray_state_rel_types" read_bytearray_state_rel_tm;
val IMP_has_io_name_tm = ``
  (asm_fetch (s1:('a,'c,'ffi) labSem$state) = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_name index s1.code``;
val _ = stmt "IMP_has_io_name" IMP_has_io_name_tm;
val _ = stmt_types "IMP_has_io_name_types" IMP_has_io_name_tm;
val bytes_in_mem_asm_write_bytearray_lemma_tm = ``
  !xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k``;
val _ = stmt "bytes_in_mem_asm_write_bytearray_lemma" bytes_in_mem_asm_write_bytearray_lemma_tm;
val _ = stmt_types "bytes_in_mem_asm_write_bytearray_lemma_types" bytes_in_mem_asm_write_bytearray_lemma_tm;
val bytes_in_mem_asm_write_bytearray_tm = ``
  (∀a. byte_align a ∈ (s1:('a,'c,'ffi) labSem$state).mem_domain ⇒ a ∈ s1.mem_domain) ∧
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
    bytes_in_mem p xs (t1:'a asm_state).mem t1.mem_domain s1.mem_domain ==>
    bytes_in_mem p xs
      (asm_write_bytearray c1 new_bytes t1.mem) t1.mem_domain s1.mem_domain``;
val _ = stmt "bytes_in_mem_asm_write_bytearray" bytes_in_mem_asm_write_bytearray_tm;
val _ = stmt_types "bytes_in_mem_asm_write_bytearray_types" bytes_in_mem_asm_write_bytearray_tm;
val write_bytearray_NOT_Loc_tm = ``
  !xs c1 (s1:('a,'c,'ffi) labSem$state) a c.
      (s1.mem a = Word c) ==>
      (write_bytearray c1 xs s1.mem s1.mem_domain s1.be) a <> Loc n n0``;
val _ = stmt "write_bytearray_NOT_Loc" write_bytearray_NOT_Loc_tm;
val _ = stmt_types "write_bytearray_NOT_Loc_types" write_bytearray_NOT_Loc_tm;
val CallFFI_bytearray_lemma_tm = ``
  byte_align (a:'a word) IN (s1:('a,'c,'ffi) labSem$state).mem_domain /\ good_dimindex (:'a) /\
    a IN (t1:'a asm_state).mem_domain /\
    a IN s1.mem_domain /\
    (s1.be = mc_conf.target.config.big_endian) /\
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) /\
    (word_loc_val_byte p labs s1.mem a mc_conf.target.config.big_endian =
       SOME (t1.mem a)) ==>
    (word_loc_val_byte p labs (write_bytearray c1 new_bytes s1.mem s1.mem_domain s1.be) a
       mc_conf.target.config.big_endian =
     SOME (asm_write_bytearray c1 new_bytes t1.mem a))``;
val _ = stmt "CallFFI_bytearray_lemma" CallFFI_bytearray_lemma_tm;
val _ = stmt_types "CallFFI_bytearray_lemma_types" CallFFI_bytearray_lemma_tm;
val list_add_if_fresh_simp_tm = ``
  !n s. list_add_if_fresh s l =
    if find_index s l n = NONE then
      APPEND l [s]
    else l``;
val _ = stmt "list_add_if_fresh_simp" list_add_if_fresh_simp_tm;
val _ = stmt_types "list_add_if_fresh_simp_types" list_add_if_fresh_simp_tm;
val find_index_append_tm = ``
  !n. find_index s (l++l') n =
  (case find_index s l n of NONE => find_index s l' (n + LENGTH l) | SOME i => SOME i)``;
val _ = stmt "find_index_append" find_index_append_tm;
val _ = stmt_types "find_index_append_types" find_index_append_tm;
val has_io_name_find_index_tm = ``
  !l s. has_io_name s (l:'a sec list)
  ==> ?y. find_index (ExtCall s) (find_ffi_names l) 0 = SOME y``;
val _ = stmt "has_io_name_find_index" has_io_name_find_index_tm;
val _ = stmt_types "has_io_name_find_index_types" has_io_name_find_index_tm;
