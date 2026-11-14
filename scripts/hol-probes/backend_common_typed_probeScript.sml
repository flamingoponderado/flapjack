(* Typed source declarations for backend_common (task 148). *)
load "preamble";
load "backend_commonTheory";
open HolKernel Parse boolLib bossLib;
open preamble backend_commonTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="backend_common",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by backend_common")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of backend_common")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "closure_tag_def_typed" "closure_tag_def";
val _ = emit "partial_app_tag_def_typed" "partial_app_tag_def";
val _ = emit "tuple_tag_def_typed" "tuple_tag_def";
val _ = emit "data_num_stubs_def_typed" "data_num_stubs_def";
val _ = emit "stack_num_stubs_def_typed" "stack_num_stubs_def";
val _ = emit "word_add_carry_def_typed" "word_add_carry_def";
val _ = emit "word_num_stubs_def_typed" "word_num_stubs_def";
val _ = emit "word_shift_def_typed" "word_shift_def";
val _ = emit "bvl_num_stub_MOD_typed" "bvl_num_stub_MOD";
val _ = emit "bvl_num_stubs_def_typed" "bvl_num_stubs_def";
val _ = emit "bvl_to_bvi_namespaces_def_typed" "bvl_to_bvi_namespaces_def";
val _ = dt_label "opw_typed" "opw";
val _ = dt_label "tra_typed" "tra";
val _ = emit "mk_cons_def_typed" "mk_cons_def";
val _ = emit "orphan_trace_def_typed" "orphan_trace_def";
val _ = emit "list_delete_def_typed" "list_delete_def";
val _ = emit "false_tag_def_typed" "false_tag_def";
val _ = emit "true_tag_def_typed" "true_tag_def";
val _ = emit "bool_to_tag_def_typed" "bool_to_tag_def";
val _ = emit "clos_tag_shift_def_typed" "clos_tag_shift_def";
val _ = emit "bind_tag_def_typed" "bind_tag_def";
val _ = emit "chr_tag_def_typed" "chr_tag_def";
val _ = emit "div_tag_def_typed" "div_tag_def";
val _ = emit "subscript_tag_def_typed" "subscript_tag_def";
val _ = emit "nil_tag_def_typed" "nil_tag_def";
val _ = emit "cons_tag_def_typed" "cons_tag_def";
val _ = emit "small_enough_int_def_typed" "small_enough_int_def";
