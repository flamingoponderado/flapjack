(* Typed source declarations for word_copy (task 148). *)
load "preamble";
load "word_copyTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_copyTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_copy",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_copy")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_copy")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "copy_state_typed" "copy_state";
val _ = emit "copy_prop_def_typed" "copy_prop_def";
val _ = emit "copy_prop_inst_def_typed" "copy_prop_inst_def";
val _ = emit "copy_prop_move_def_typed" "copy_prop_move_def";
val _ = emit "copy_prop_prog_def_typed" "copy_prop_prog_def";
val _ = emit "copy_prop_share_def_typed" "copy_prop_share_def";
val _ = emit "empty_eq_def_typed" "empty_eq_def";
val _ = emit "lookup_eq_def_typed" "lookup_eq_def";
val _ = emit "lookup_eq_imm_def_typed" "lookup_eq_imm_def";
val _ = emit "lookup_store_eq_def_typed" "lookup_store_eq_def";
val _ = emit "merge_eqs_def_typed" "merge_eqs_def";
val _ = emit "remove_eq_def_typed" "remove_eq_def";
val _ = emit "remove_eqs_def_typed" "remove_eqs_def";
val _ = emit "set_eq_def_typed" "set_eq_def";
val _ = emit "set_store_eq_def_typed" "set_store_eq_def";
