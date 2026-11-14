(* Typed source declarations for word_unreachProof (task 148). *)
load "preamble";
load "word_unreachProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_unreachProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_unreachProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_unreachProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_unreachProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "ALL_DISTINCT_merge_moves_typed" "ALL_DISTINCT_merge_moves";
val _ = emit "copy_vars_def_typed" "copy_vars_def";
val _ = emit "copy_vars_anub_typed" "copy_vars_anub";
val _ = emit "copy_vars_append_typed" "copy_vars_append";
val _ = emit "copy_vars_MEM_acc_typed" "copy_vars_MEM_acc";
val _ = emit "evaluate_Move_typed" "evaluate_Move";
val _ = emit "evaluate_remove_unreach_typed" "evaluate_remove_unreach";
val _ = emit "evaluate_Seq_assoc_typed" "evaluate_Seq_assoc";
val _ = emit "evaluate_Seq_assoc_right_lemma_typed" "evaluate_Seq_assoc_right_lemma";
val _ = emit "evaluate_Seq_Skip_typed" "evaluate_Seq_Skip";
val _ = emit "evaluate_Skip_Seq_typed" "evaluate_Skip_Seq";
val _ = emit "IMP_EVERY_MAP_SND_anub_typed" "IMP_EVERY_MAP_SND_anub";
val _ = emit "lookup_copy_vars_typed" "lookup_copy_vars";
val _ = emit "lookup_copy_vars_ignore_typed" "lookup_copy_vars_ignore";
val _ = emit "merge_moves_Skip_typed" "merge_moves_Skip";
val _ = emit "merge_moves_thm_typed" "merge_moves_thm";
