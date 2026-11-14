(* Typed source declarations for word_simp (task 148). *)
load "preamble";
load "word_simpTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_simpTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_simp",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_simp")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_simp")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "all_names_def_typed" "all_names_def";
val _ = emit "compile_exp_def_typed" "compile_exp_def";
val _ = emit "const_fp_def_typed" "const_fp_def";
val _ = emit "const_fp_exp_def_typed" "const_fp_exp_def";
val _ = emit "const_fp_inst_cs_def_typed" "const_fp_inst_cs_def";
val _ = emit "const_fp_loop_def_typed" "const_fp_loop_def";
val _ = emit "const_fp_move_cs_def_typed" "const_fp_move_cs_def";
val _ = emit "dest_If_def_typed" "dest_If_def";
val _ = emit "dest_If_Eq_Imm_def_typed" "dest_If_Eq_Imm_def";
val _ = emit "dest_Raise_num_pmatch_def_typed" "dest_Raise_num_pmatch_def";
val _ = emit "dest_Seq_def_typed" "dest_Seq_def";
val _ = emit "dest_Seq_Assign_Const_def_typed" "dest_Seq_Assign_Const_def";
val _ = emit "drop_consts_def_typed" "drop_consts_def";
val _ = emit "get_var_imm_cs_def_typed" "get_var_imm_cs_def";
val _ = emit "is_gc_const_def_typed" "is_gc_const_def";
val _ = emit "is_simple_pmatch_def_typed" "is_simple_pmatch_def";
val _ = emit "push_out_if_def_typed" "push_out_if_def";
val _ = emit "push_out_if_aux_def_typed" "push_out_if_aux_def";
val _ = emit "rewrite_duplicate_if_max_reassoc_def_typed" "rewrite_duplicate_if_max_reassoc_def";
val _ = emit "Seq_assoc_def_typed" "Seq_assoc_def";
val _ = emit "simp_duplicate_if_def_typed" "simp_duplicate_if_def";
val _ = emit "SmartSeq_def_typed" "SmartSeq_def";
val _ = emit "strip_const_def_typed" "strip_const_def";
val _ = emit "try_if_hoist1_def_typed" "try_if_hoist1_def";
val _ = emit "try_if_hoist2_def_typed" "try_if_hoist2_def";
