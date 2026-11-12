(* Typed source declarations for flat_elim (task 148). *)
load "preamble";
load "flat_elimTheory";
open HolKernel Parse boolLib bossLib;
open preamble flat_elimTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="flat_elim",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by flat_elim")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of flat_elim")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "remove_flat_prog_def_typed" "remove_flat_prog_def";
val _ = emit "is_hidden_def_typed" "is_hidden_def";
val _ = emit "total_pat_def_typed" "total_pat_def";
val _ = emit "is_pure_def_typed" "is_pure_def";
val _ = emit "has_Eval_def_typed" "has_Eval_def";
val _ = emit "dest_GlobalVarInit_def_typed" "dest_GlobalVarInit_def";
val _ = emit "dest_GlobalVarLookup_def_typed" "dest_GlobalVarLookup_def";
val _ = emit "find_loc_def_typed" "find_loc_def";
val _ = emit "find_lookups_def_typed" "find_lookups_def";
val _ = emit "analyse_exp_def_typed" "analyse_exp_def";
val _ = emit "code_analysis_union_def_typed" "code_analysis_union_def";
val _ = emit "analyse_code_def_typed" "analyse_code_def";
val _ = emit "keep_def_typed" "keep_def";
val _ = emit "remove_unreachable_def_typed" "remove_unreachable_def";
val _ = emit "has_Eval_dec_def_typed" "has_Eval_dec_def";
