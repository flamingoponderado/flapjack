(*
  Direct HOL EVAL oracle for the exact loop_to_word context definitions at
  cakeml/pancake/loop_to_wordScript.sml:10-53:

    find_var_def      (:10-15)
    find_reg_imm_def  (:17-20)
    toNumSet_def      (:42-45)
    fromNumSet_def    (:47-48)
    mk_new_cutset_def (:51-53)
    make_ctxt_def     (:150-153)

  This is intentionally a HOL script rather than a second implementation; the
  checked-in output is captured from a direct HOL invocation of this file.
  The kernel-checked Lean replay is Flapjack.Test.LoopToWordExactParity.
*)
load "bossLib";
load "preamble";
load "loop_to_wordTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

val ctxt = ``insert 3 7 (insert 5 9 (LN : num num_map))``;
val live = ``insert 3 () (insert 5 () (LN : unit spt))``;

(* find_var_def, loop_to_wordScript.sml:10-15 *)
print_eval "lt_find_var_hit" ``find_var ^ctxt 5``;
print_eval "lt_find_var_miss" ``find_var ^ctxt 4``;

(* find_reg_imm_def, loop_to_wordScript.sml:17-20 *)
print_eval "lt_find_reg_imm_imm" ``find_reg_imm ^ctxt (Imm 5w : 64 reg_imm)``;
print_eval "lt_find_reg_imm_reg" ``find_reg_imm ^ctxt (Reg 5 : 64 reg_imm)``;

(* toNumSet_def, loop_to_wordScript.sml:42-45 *)
print_eval "lt_to_num_set_lookup0" ``lookup 0 (toNumSet [1;2;3])``;
print_eval "lt_to_num_set_lookup2" ``lookup 2 (toNumSet [1;2;3])``;
print_eval "lt_to_num_set_lookup3" ``lookup 3 (toNumSet [1;2;3])``;

(* fromNumSet_def, loop_to_wordScript.sml:47-48 *)
print_eval "lt_from_num_set" ``fromNumSet (insert 3 () (insert 1 () (LN : unit spt)))``;

(* mk_new_cutset_def, loop_to_wordScript.sml:51-53 *)
print_eval "lt_mk_new_cutset_lookup0" ``lookup 0 (mk_new_cutset ^ctxt ^live)``;
print_eval "lt_mk_new_cutset_lookup5" ``lookup 5 (mk_new_cutset ^ctxt ^live)``;
print_eval "lt_mk_new_cutset_absent" ``lookup 2 (mk_new_cutset ^ctxt ^live)``;

(* make_ctxt_def, loop_to_wordScript.sml:150-153 *)
print_eval "lt_make_ctxt_lookup3"
  ``lookup 3 (make_ctxt 2 [3;5] (LN : num num_map))``;
print_eval "lt_make_ctxt_lookup5"
  ``lookup 5 (make_ctxt 2 [3;5] (LN : num num_map))``;
print_eval "lt_make_ctxt_lookup7"
  ``lookup 7 (make_ctxt 2 [3;5] (LN : num num_map))``;
