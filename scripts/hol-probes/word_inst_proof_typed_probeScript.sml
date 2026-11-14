(* Typed source declarations for word_instProof (task 148). *)
load "preamble";
load "word_instProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_instProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_instProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_instProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_instProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "inst_select_Loop_helper_typed" "inst_select_Loop_helper";
val _ = emit "inst_select_thm_typed" "inst_select_thm";
val _ = emit "binary_branch_exp_def_typed" "binary_branch_exp_def";
val _ = emit "pull_ops_simp_def_typed" "pull_ops_simp_def";
val _ = emit "evaluate_three_to_two_reg_prog_typed" "evaluate_three_to_two_reg_prog";
val _ = emit "three_to_two_reg_Loop_typed" "three_to_two_reg_Loop";
val _ = emit "three_to_two_reg_correct_typed" "three_to_two_reg_correct";
