(* Typed statements of the no_mutcons lemmas in bvl_to_bviProof.

   compile_inc_no_mutcons and bvi_tailrec_compile_prog_no_mutcons are exported
   by the theory and are shown directly.  The remaining lemmas are [local] in
   the source proof script and are therefore not in the theory database; their
   statements are transcribed from bvl_to_bviProofScript.sml:4811-5090 and
   replayed here as typed terms. *)
load "preamble";
load "bvl_to_bviProofTheory";
load "bvi_tailrecTheory";
load "miscTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_to_bviProofTheory bvi_tailrecTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun replay label term = (print (label ^ "="); print_term term; print "\n");

val _ = show "compile_inc_no_mutcons_typed" bvl_to_bviProofTheory.compile_inc_no_mutcons;
val _ = show "bvi_tailrec_compile_prog_no_mutcons_typed"
  bvl_to_bviProofTheory.bvi_tailrec_compile_prog_no_mutcons;

val _ = replay "bvi_let_delete_var_no_mutcons_typed"
  ``!x. no_mutcons x ==> no_mutcons (bvi_let$delete_var x)``;
val _ = replay "bvi_let_compile_no_mutcons_typed"
  ``(!env d e. no_mutcons e ==> no_mutcons (bvi_let$compile_sing env d e)) /\
    (!env d es. EVERY no_mutcons es ==> EVERY no_mutcons (bvi_let$compile_list env d es))``;
val _ = replay "bvi_let_compile_exp_no_mutcons_typed"
  ``!x. no_mutcons x ==> no_mutcons (bvi_let$compile_exp x)``;
val _ = replay "compile_int_no_mutcons_typed"
  ``!i. no_mutcons (bvl_to_bvi$compile_int i)``;
val _ = replay "compile_op_no_mutcons_typed"
  ``!op c1. EVERY no_mutcons c1 ==> no_mutcons (bvl_to_bvi$compile_op op c1)``;
val _ = replay "compile_exps_sing_no_mutcons_typed"
  ``(!n e c aux n1.
      bvl_to_bvi$compile_exps_sing n e = (c,aux,n1) ==>
      no_mutcons c /\ EVERY (no_mutcons o SND o SND) (misc$append aux)) /\
    (!n es c aux n1.
      bvl_to_bvi$compile_exps_list n es = (c,aux,n1) ==>
      EVERY no_mutcons c /\ EVERY (no_mutcons o SND o SND) (misc$append aux))``;
val _ = replay "compile_single_no_mutcons_typed"
  ``!n p q n1. bvl_to_bvi$compile_single n p = (q,n1) ==>
      EVERY (no_mutcons o SND o SND) (misc$append q)``;
val _ = replay "compile_list_no_mutcons_typed"
  ``!n progs q n1. bvl_to_bvi$compile_list n progs = (q,n1) ==>
      EVERY (no_mutcons o SND o SND) (misc$append q)``;
val _ = replay "stubs_no_mutcons_typed"
  ``!start n. EVERY (no_mutcons o SND o SND) (bvl_to_bvi$stubs start n)``;
val _ = replay "to_op_no_mutcons_typed"
  ``!op. no_mutcons_op (bvi_tailrec$to_op op)``;
val _ = replay "apply_op_no_mutcons_typed"
  ``!op e1 e2. no_mutcons (bvi_tailrec$apply_op op e1 e2) <=> no_mutcons e1 /\ no_mutcons e2``;
val _ = replay "id_from_op_no_mutcons_typed"
  ``!op. no_mutcons (bvi_tailrec$id_from_op op)``;
val _ = replay "let_wrap_no_mutcons_typed"
  ``!arity id x. no_mutcons (bvi_tailrec$let_wrap arity id x) <=> no_mutcons id /\ no_mutcons x``;
val _ = replay "get_bin_args_no_mutcons_typed"
  ``!exp e1 e2. bvi_tailrec$get_bin_args exp = SOME (e1,e2) /\ no_mutcons exp ==>
      no_mutcons e1 /\ no_mutcons e2``;
val _ = replay "opbinargs_no_mutcons_typed"
  ``!opr exp e1 e2. bvi_tailrec$opbinargs opr exp = SOME (e1,e2) /\ no_mutcons exp ==>
      no_mutcons e1 /\ no_mutcons e2``;
val _ = replay "try_swap_no_mutcons_typed"
  ``!loc opr exp. no_mutcons exp ==> no_mutcons (bvi_tailrec$try_swap loc opr exp)``;
val _ = replay "check_op_no_mutcons_typed"
  ``!ts opr loc exp exp2. bvi_tailrec$check_op ts opr loc exp = SOME exp2 /\ no_mutcons exp ==>
      no_mutcons exp2``;
val _ = replay "args_from_no_mutcons_typed"
  ``!f t d args hdl. bvi_tailrec$args_from f = SOME (t,d,args,hdl) /\ no_mutcons f ==>
      EVERY no_mutcons args /\ (case hdl of NONE => T | SOME h => no_mutcons h)``;
val _ = replay "push_call_no_mutcons_typed"
  ``!n op acc x f. no_mutcons x /\ no_mutcons f ==>
      no_mutcons (bvi_tailrec$push_call n op acc x (bvi_tailrec$args_from f))``;
val _ = replay "rewrite_catchall_no_mutcons_typed"
  ``!ts opr loc exp next acc r y.
      (case bvi_tailrec$check_op ts opr loc exp of
         NONE => (F, bvi_tailrec$apply_op opr (bvi$Var acc) exp)
       | SOME v1 =>
           case bvi_tailrec$opbinargs opr v1 of
             NONE => (F, bvi_tailrec$apply_op opr (bvi$Var acc) v1)
           | SOME (xs,f) => (T, bvi_tailrec$push_call next opr acc xs (bvi_tailrec$args_from f)))
      = (r,y) /\
      no_mutcons exp ==> no_mutcons y``;
val _ = replay "rewrite_no_mutcons_typed"
  ``!loc next opr acc ts exp r y.
      bvi_tailrec$rewrite loc next opr acc ts exp = (r,y) /\ no_mutcons exp ==> no_mutcons y``;
val _ = replay "tailrec_compile_exp_no_mutcons_typed"
  ``!loc next arity exp aux opt.
      bvi_tailrec$compile_exp loc next arity exp = SOME (aux,opt) /\ no_mutcons exp ==>
      no_mutcons aux /\ no_mutcons opt``;
val _ = replay "bvi_tailrec_compile_each_no_mutcons_typed"
  ``!next prog next1 prog1.
      bvi_tailrec$compile_each next prog = (next1,prog1) /\
      EVERY (no_mutcons o SND o SND) prog ==>
      EVERY (no_mutcons o SND o SND) prog1``;

val _ = show "compile_get_code_labels_typed" bvl_to_bviProofTheory.compile_get_code_labels;
