(* Typed source declarations for bvl_inlineProof (task 148). *)
load "preamble";
load "bvl_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_inlineProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvl_inlineProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvl_inlineProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvl_inlineProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "evaluate_remove_ticks_typed" "evaluate_remove_ticks";
val _ = emit "remove_ticks_cc_def_typed" "remove_ticks_cc_def";
val _ = emit "remove_ticks_co_def_typed" "remove_ticks_co_def";
val _ = emit "evaluate_compile_prog_typed" "evaluate_compile_prog";
val _ = emit "subspt_exp_rel_typed" "subspt_exp_rel";
val _ = emit "exp_rel_swap_typed" "exp_rel_swap";
val _ = emit "exp_rel_refl_typed" "exp_rel_refl";
val _ = emit "exp_rel_tick_inline_typed" "exp_rel_tick_inline";
val _ = emit "tick_inline_all_names_typed" "tick_inline_all_names";
val _ = emit "in_cc_def_typed" "in_cc_def";
val _ = emit "in_co_def_typed" "in_co_def";
val _ = emit "in_state_rel_def_typed" "in_state_rel_def";
val _ = emit "MAP_FST_tick_inline_all_typed" "MAP_FST_tick_inline_all";
val _ = emit "evaluate_inline_typed" "evaluate_inline";
val _ = emit "tick_compile_prog_res_range_typed" "tick_compile_prog_res_range";
val _ = emit "LENGTH_let_op_typed" "LENGTH_let_op";
val _ = emit "HD_let_op_typed" "HD_let_op";
