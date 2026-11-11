(* Typed source declarations for bvi_tailrec. *)
load "preamble";
load "bvi_tailrecTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_tailrecTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

fun show_type label term = (print (label ^ "="); print_type (type_of term); print "\n");

val _ = print ("v_ty_typed=" ^
  String.concatWith "; "
    (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end)
      [``bvi_tailrec$Int``, ``bvi_tailrec$List``, ``bvi_tailrec$Any``]) ^ "\n");
val _ = print ("assoc_op_typed=" ^
  String.concatWith "; "
    (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end)
      [``bvi_tailrec$Plus``, ``bvi_tailrec$Times``, ``bvi_tailrec$Append``, ``bvi_tailrec$Noop``]) ^ "\n");

val _ = show "is_rec_def_typed" bvi_tailrecTheory.is_rec_def;
val _ = show "from_op_def_typed" bvi_tailrecTheory.from_op_def;
val _ = show "to_op_def_typed" bvi_tailrecTheory.to_op_def;
val _ = show "apply_op_def_typed" bvi_tailrecTheory.apply_op_def;
val _ = show "arg_ty_def_typed" bvi_tailrecTheory.arg_ty_def;
val _ = show "check_op_def_typed" bvi_tailrecTheory.check_op_def;
val _ = show "decide_ty_def_typed" bvi_tailrecTheory.decide_ty_def;
val _ = show "get_bin_args_def_typed" bvi_tailrecTheory.get_bin_args_def;
val _ = show "is_arith_def_typed" bvi_tailrecTheory.is_arith_def;
val _ = show "is_const_def_typed" bvi_tailrecTheory.is_const_def;
val _ = show "is_rel_def_typed" bvi_tailrecTheory.is_rel_def;
val _ = show "opbinargs_def_typed" bvi_tailrecTheory.opbinargs_def;
val _ = show "op_eq_def_typed" bvi_tailrecTheory.op_eq_def;
val _ = show "op_type_def_typed" bvi_tailrecTheory.op_type_def;
val _ = show "scan_expr_sing_def_typed" bvi_tailrecTheory.scan_expr_sing_def;
val _ = show "term_ok_def_typed" bvi_tailrecTheory.term_ok_def;
val _ = show "term_ok_any_def_typed" bvi_tailrecTheory.term_ok_any_def;
val _ = show "term_ok_int_def_typed" bvi_tailrecTheory.term_ok_int_def;
val _ = show "try_swap_def_typed" bvi_tailrecTheory.try_swap_def;
val _ = show "has_rec_def_typed" bvi_tailrecTheory.has_rec_def;
val _ = show "has_rec1_def_typed" bvi_tailrecTheory.has_rec1_def;
val _ = show "has_rec_sing_def_typed" bvi_tailrecTheory.has_rec_sing_def;
val _ = show "has_rec_eq_typed" bvi_tailrecTheory.has_rec_eq;
val _ = show "args_from_def_typed" bvi_tailrecTheory.args_from_def;
val _ = show "id_from_op_def_typed" bvi_tailrecTheory.id_from_op_def;
val _ = show "let_wrap_def_typed" bvi_tailrecTheory.let_wrap_def;
val _ = show "mk_aux_call_def_typed" bvi_tailrecTheory.mk_aux_call_def;
val _ = show "push_call_def_typed" bvi_tailrecTheory.push_call_def;
val _ = show "dummy_def_typed" bvi_tailrecTheory.dummy_def;
