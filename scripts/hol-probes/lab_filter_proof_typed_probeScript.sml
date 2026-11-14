(* Typed source declarations for lab_filterProof (task 148). *)
load "preamble";
load "lab_filterProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble lab_filterProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="lab_filterProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by lab_filterProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of lab_filterProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "filter_correct_typed" "filter_correct";
val _ = emit "adjust_pc_def_typed" "adjust_pc_def";
val _ = emit "all_skips_def_typed" "all_skips_def";
val _ = emit "asm_fetch_aux_eq_typed" "asm_fetch_aux_eq";
val _ = emit "sec_ends_with_label_filter_skip_typed" "sec_ends_with_label_filter_skip";
val _ = emit "filter_skip_semantics_typed" "filter_skip_semantics";
val _ = emit "share_mem_op_FFI_final_filter_correct_typed" "share_mem_op_FFI_final_filter_correct";
val _ = emit "share_mem_op_FFI_return_filter_correct_typed" "share_mem_op_FFI_return_filter_correct";
val _ = emit "share_mem_op_NONE_filter_correct_typed" "share_mem_op_NONE_filter_correct";
val _ = emit "state_rel_def_typed" "state_rel_def";
