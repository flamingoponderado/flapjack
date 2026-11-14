(* Typed source declarations for bvl_inline (task 148). *)
load "preamble";
load "bvl_inlineTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_inlineTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvl_inline",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvl_inline")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvl_inline")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "optimise_def_typed" "optimise_def";
val _ = emit "optimise_eq_typed" "optimise_eq";
val _ = emit "compile_inc_def_typed" "compile_inc_def";
val _ = emit "compile_prog_def_typed" "compile_prog_def";
val _ = emit "remove_ticks_sing_def_typed" "remove_ticks_sing_def";
val _ = emit "remove_ticks_def_typed" "remove_ticks_def";
val _ = emit "remove_ticks_sing_typed" "remove_ticks_sing";
val _ = emit "tick_inline_sing_def_typed" "tick_inline_sing_def";
val _ = emit "tick_inline_def_typed" "tick_inline_def";
val _ = emit "tick_inline_sing_typed" "tick_inline_sing";
val _ = emit "is_small_sing_def_typed" "is_small_sing_def";
val _ = emit "is_small_aux_def_typed" "is_small_aux_def";
val _ = emit "is_small_sing_typed" "is_small_sing";
val _ = emit "is_small_def_typed" "is_small_def";
val _ = emit "is_rec_sing_def_typed" "is_rec_sing_def";
val _ = emit "is_rec_def_typed" "is_rec_def";
val _ = emit "is_rec_sing_typed" "is_rec_sing";
val _ = emit "must_inline_def_typed" "must_inline_def";
val _ = emit "tick_inline_all_def_typed" "tick_inline_all_def";
val _ = emit "tick_compile_prog_def_typed" "tick_compile_prog_def";
val _ = emit "var_list_def_typed" "var_list_def";
val _ = emit "dest_op_def_typed" "dest_op_def";
val _ = emit "let_op_one_def_typed" "let_op_one_def";
val _ = emit "let_op_def_typed" "let_op_def";
val _ = emit "let_op_sing_def_typed" "let_op_sing_def";
val _ = emit "let_op_one_typed" "let_op_one";
