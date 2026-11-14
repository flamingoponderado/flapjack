(* Typed source declarations for stack_rawcallProof (task 148). *)
load "preamble";
load "stack_rawcallProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_rawcallProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_rawcallProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_rawcallProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "stack_alloc_stack_asm_convs_typed" "stack_alloc_stack_asm_convs";
val _ = emit "stack_asm_name_comp_typed" "stack_asm_name_comp";
val _ = emit "comp_correct_typed" "comp_correct";
val _ = emit "comp_LN_typed" "comp_LN";
val _ = emit "comp_seq_neq_IMP_typed" "comp_seq_neq_IMP";
val _ = emit "domain_fromAList_compile_typed" "domain_fromAList_compile";
val _ = emit "lookup_collect_info_typed" "lookup_collect_info";
val _ = emit "state_ok_collect_info_typed" "state_ok_collect_info";
val _ = emit "compile_semantics_typed" "compile_semantics";
val _ = emit "call_arg_comp_typed" "call_arg_comp";
val _ = emit "call_args_comp_typed" "call_args_comp";
val _ = emit "MAP_FST_compile_typed" "MAP_FST_compile";
val _ = emit "reg_bound_comp_typed" "reg_bound_comp";
val _ = emit "stack_alloc_call_args_typed" "stack_alloc_call_args";
val _ = emit "stack_rawcall_reg_bound_typed" "stack_rawcall_reg_bound";
val _ = emit "extract_labels_comp_typed" "extract_labels_comp";
val _ = emit "stack_get_handler_labels_comp_typed" "stack_get_handler_labels_comp";
val _ = emit "evaluate_comp_Inst_typed" "evaluate_comp_Inst";
val _ = emit "get_labels_comp_typed" "get_labels_comp";
val _ = emit "state_ok_def_typed" "state_ok_def";
val _ = emit "state_rel_def_typed" "state_rel_def";
