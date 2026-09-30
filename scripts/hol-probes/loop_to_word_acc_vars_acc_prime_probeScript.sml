(*
  Direct HOL EVAL observations for loop_to_wordProof$acc_vars_acc'.

  Reference: cakeml/pancake/proofs/loop_to_wordProofScript.sml:979-980, which
  specialises loopProps$acc_vars_acc
  (`!p l. domain (acc_vars p l) = domain (acc_vars p LN) UNION domain l`,
  cakeml/pancake/semantics/loopPropsScript.sml:89) at l := acc_vars q LN.

  Each row prints two booleans: whether a concrete variable is in the domain of
  the left-hand side `acc_vars p (acc_vars q LN)` and whether it is in the
  right-hand side set `domain (acc_vars p LN) UNION domain (acc_vars q LN)`.
  The statement is the set equality, so for every key the two booleans must
  agree.  The programs exercise Assign, Seq, If, Loop and Call.
*)
load "bossLib";
load "preamble";
load "loop_to_wordProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordProofTheory;

fun print_pair label lhs rhs =
  let
    val thl = EVAL lhs
    val thr = EVAL rhs
  in
    print (label ^ "=(");
    print (term_to_string (rconc thl));
    print ",";
    print (term_to_string (rconc thr));
    print ")\n"
  end;

(* Assign: p assigns 10, q assigns 1. *)
val p_assign = ``loopLang$Assign 10 (loopLang$Const (0w : 32 word))``;
val q_assign = ``loopLang$Assign 1 (loopLang$Const (0w : 32 word))``;
val _ = print_pair "assign_lhs_key"
  ``10 IN domain (acc_vars ^p_assign (acc_vars ^q_assign LN))``
  ``10 IN (domain (acc_vars ^p_assign LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "assign_q_key"
  ``1 IN domain (acc_vars ^p_assign (acc_vars ^q_assign LN))``
  ``1 IN (domain (acc_vars ^p_assign LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "assign_absent_key"
  ``99 IN domain (acc_vars ^p_assign (acc_vars ^q_assign LN))``
  ``99 IN (domain (acc_vars ^p_assign LN) UNION domain (acc_vars ^q_assign LN))``;

(* Seq: p assigns 10 and 11, q assigns 1. *)
val p_seq = ``loopLang$Seq (loopLang$Assign 10 (loopLang$Const (0w : 32 word)))
  (loopLang$Assign 11 (loopLang$Const (0w : 32 word)))``;
val _ = print_pair "seq_p_first"
  ``10 IN domain (acc_vars ^p_seq (acc_vars ^q_assign LN))``
  ``10 IN (domain (acc_vars ^p_seq LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "seq_p_second"
  ``11 IN domain (acc_vars ^p_seq (acc_vars ^q_assign LN))``
  ``11 IN (domain (acc_vars ^p_seq LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "seq_q_key"
  ``1 IN domain (acc_vars ^p_seq (acc_vars ^q_assign LN))``
  ``1 IN (domain (acc_vars ^p_seq LN) UNION domain (acc_vars ^q_assign LN))``;

(* If: p assigns 10 on the then branch and 11 on the else branch. *)
val p_if = ``loopLang$If asm$Equal 3 (asm$Reg 4)
  (loopLang$Assign 10 (loopLang$Const (0w : 32 word)))
  (loopLang$Assign 11 (loopLang$Const (0w : 32 word))) LN``;
val _ = print_pair "if_then_key"
  ``10 IN domain (acc_vars ^p_if (acc_vars ^q_assign LN))``
  ``10 IN (domain (acc_vars ^p_if LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "if_else_key"
  ``11 IN domain (acc_vars ^p_if (acc_vars ^q_assign LN))``
  ``11 IN (domain (acc_vars ^p_if LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "if_absent_key"
  ``12 IN domain (acc_vars ^p_if (acc_vars ^q_assign LN))``
  ``12 IN (domain (acc_vars ^p_if LN) UNION domain (acc_vars ^q_assign LN))``;

(* Loop: p's loop body assigns 10, q's body assigns 2. *)
val p_loop = ``loopLang$Loop LN
  (loopLang$Assign 10 (loopLang$Const (0w : 32 word))) LN``;
val q_loop = ``loopLang$Loop LN
  (loopLang$Assign 2 (loopLang$Const (0w : 32 word))) LN``;
val _ = print_pair "loop_p_key"
  ``10 IN domain (acc_vars ^p_loop (acc_vars ^q_loop LN))``
  ``10 IN (domain (acc_vars ^p_loop LN) UNION domain (acc_vars ^q_loop LN))``;
val _ = print_pair "loop_q_key"
  ``2 IN domain (acc_vars ^p_loop (acc_vars ^q_loop LN))``
  ``2 IN (domain (acc_vars ^p_loop LN) UNION domain (acc_vars ^q_loop LN))``;

(* Call: p returns [10;11] into its normal-return handler; q assigns 1. *)
val p_call = ``loopLang$Call (SOME ([10; 11], LN)) (SOME 3) [4; 5] NONE``;
val _ = print_pair "call_return_first"
  ``10 IN domain (acc_vars ^p_call (acc_vars ^q_assign LN))``
  ``10 IN (domain (acc_vars ^p_call LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "call_return_second"
  ``11 IN domain (acc_vars ^p_call (acc_vars ^q_assign LN))``
  ``11 IN (domain (acc_vars ^p_call LN) UNION domain (acc_vars ^q_assign LN))``;
val _ = print_pair "call_q_key"
  ``1 IN domain (acc_vars ^p_call (acc_vars ^q_assign LN))``
  ``1 IN (domain (acc_vars ^p_call LN) UNION domain (acc_vars ^q_assign LN))``;
