(* Typed source declarations for pattern_comp (task 148). *)
load "preamble";
load "pattern_compTheory";
open HolKernel Parse boolLib bossLib;
open preamble pattern_compTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="pattern_comp",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by pattern_comp")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of pattern_comp")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "is_const_row_def_typed" "is_const_row_def";
val _ = emit "is_Any_def_typed" "is_Any_def";
val _ = emit "is_Or_row_def_typed" "is_Or_row_def";
val _ = emit "take_until_Any_def_typed" "take_until_Any_def";
val _ = emit "move_const_up_def_typed" "move_const_up_def";
val _ = emit "insert_Any_def_typed" "insert_Any_def";
val _ = emit "is_True_def_typed" "is_True_def";
val _ = emit "mk_Disj_def_typed" "mk_Disj_def";
val _ = emit "mk_Conj_def_typed" "mk_Conj_def";
val _ = emit "mk_If_def_typed" "mk_If_def";
val _ = emit "get_pos_def_typed" "get_pos_def";
val _ = emit "pat_to_guard_def_typed" "pat_to_guard_def";
val _ = emit "pats_to_code_def_typed" "pats_to_code_def";
val _ = emit "pmatch_list_LENGTH_typed" "pmatch_list_LENGTH";
val _ = emit "is_Any_pmatch_typed" "is_Any_pmatch";
val _ = emit "match_take_until_Any_typed" "match_take_until_Any";
val _ = emit "match_append_typed" "match_append";
val _ = emit "pmatchResult_case_NONE_typed" "pmatchResult_case_NONE";
val _ = emit "is_const_row_lemma_typed" "is_const_row_lemma";
val _ = emit "not_is_const_row_typed" "not_is_const_row";
val _ = emit "EVERY_take_until_Any_typed" "EVERY_take_until_Any";
val _ = emit "matdch_FILTER_NOT_NONE_typed" "matdch_FILTER_NOT_NONE";
val _ = emit "match_move_const_up_typed" "match_move_const_up";
val _ = emit "match_insert_Any_typed" "match_insert_Any";
val _ = emit "walk_def_typed" "walk_def";
val _ = emit "walk_list_def_typed" "walk_list_def";
val _ = emit "app_pos_Pos_typed" "app_pos_Pos";
val _ = emit "walk_thm_typed" "walk_thm";
val _ = emit "walk_append_typed" "walk_append";
val _ = emit "dt_eval_guard_pat_to_guard_typed" "dt_eval_guard_pat_to_guard";
val _ = emit "pat_to_code_thm_typed" "pat_to_code_thm";
val _ = emit "comp_thm_typed" "comp_thm";
val _ = emit "comp_def_typed" "comp_def";
