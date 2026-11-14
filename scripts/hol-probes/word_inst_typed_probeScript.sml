(* Typed source declarations for word_inst (task 148). *)
load "preamble";
load "word_instTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_instTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_inst",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_inst")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_inst")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "convert_sub_def_typed" "convert_sub_def";
val _ = emit "flatten_exp_def_typed" "flatten_exp_def";
val _ = emit "inst_select_def_typed" "inst_select_def";
val _ = emit "inst_select_exp_def_typed" "inst_select_exp_def";
val _ = emit "is_const_def_typed" "is_const_def";
val _ = emit "is_Lookup_CurrHeap_def_typed" "is_Lookup_CurrHeap_def";
val _ = emit "op_consts_def_typed" "op_consts_def";
val _ = emit "optimize_consts_def_typed" "optimize_consts_def";
val _ = emit "pull_exp_def_typed" "pull_exp_def";
val _ = emit "pull_ops_def_typed" "pull_ops_def";
val _ = emit "reduce_const_def_typed" "reduce_const_def";
val _ = emit "rm_const_def_typed" "rm_const_def";
val _ = emit "three_to_two_reg_def_typed" "three_to_two_reg_def";
val _ = emit "three_to_two_reg_prog_def_typed" "three_to_two_reg_prog_def";
