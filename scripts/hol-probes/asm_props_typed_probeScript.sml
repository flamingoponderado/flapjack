(* Typed source declarations for asmProps (task 148). *)
load "preamble";
load "asmPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="asmProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by asmProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of asmProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "arith_upd_consts_typed" "arith_upd_consts";
val _ = emit "binop_upd_consts_typed" "binop_upd_consts";
val _ = emit "upd_pc_simps_typed" "upd_pc_simps";
val _ = emit "asm_consts_typed" "asm_consts";
val _ = emit "asm_failed_ignore_new_pc_typed" "asm_failed_ignore_new_pc";
val _ = emit "asm_mem_ignore_new_pc_typed" "asm_mem_ignore_new_pc";
val _ = emit "asserts_def_typed" "asserts_def";
val _ = emit "asserts2_def_typed" "asserts2_def";
val _ = emit "asserts2_change_interfer_typed" "asserts2_change_interfer";
val _ = emit "asserts2_every_typed" "asserts2_every";
val _ = emit "asserts2_first_typed" "asserts2_first";
val _ = emit "asserts_IMP_FOLDR_COUNT_LIST_typed" "asserts_IMP_FOLDR_COUNT_LIST";
val _ = emit "asserts_IMP_FOLDR_COUNT_LIST_LESS_typed" "asserts_IMP_FOLDR_COUNT_LIST_LESS";
val _ = emit "asserts_WEAKEN_typed" "asserts_WEAKEN";
val _ = emit "encoder_correct_def_typed" "encoder_correct_def";
val _ = emit "enc_ok_def_typed" "enc_ok_def";
val _ = emit "offset_monotonic_def_typed" "offset_monotonic_def";
val _ = emit "target_ok_def_typed" "target_ok_def";
val _ = emit "fp_upd_consts_typed" "fp_upd_consts";
val _ = emit "interference_ok_def_typed" "interference_ok_def";
val _ = emit "read_mem_word_IMP_mem_eq_typed" "read_mem_word_IMP_mem_eq";
val _ = emit "write_mem_word_mem_domain_typed" "write_mem_word_mem_domain";
val _ = emit "write_mem_word_mem_eq_typed" "write_mem_word_mem_eq";
val _ = emit "all_pcs_def_typed" "all_pcs_def";
val _ = emit "all_pcs_thm_typed" "all_pcs_thm";
val _ = emit "bytes_in_memory_all_pcs_typed" "bytes_in_memory_all_pcs";
val _ = dt_label "target_typed" "target";
val _ = emit "target_state_rel_def_typed" "target_state_rel_def";
