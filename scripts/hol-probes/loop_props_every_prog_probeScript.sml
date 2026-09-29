(* Direct HOL-EVAL fixture for loopProps$every_prog_def. *)
load "bossLib";
load "preamble";
load "../semantics/loopPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* A predicate that fails exactly at Loop nodes, so each clause's recursion --
   including the two handler branches -- is observable. *)
val noloop = ``\(p : 8 loopLang$prog). case p of Loop l1 b l2 => F | _ => T``;

val _ = print_eval "ep_skip"
  ``every_prog ^noloop (Skip : 8 loopLang$prog)``;
val _ = print_eval "ep_assign"
  ``every_prog ^noloop ((Assign 3 (Const 0w)) : 8 loopLang$prog)``;
val _ = print_eval "ep_seq"
  ``every_prog ^noloop ((Seq Skip Skip) : 8 loopLang$prog)``;
val _ = print_eval "ep_seq_loop"
  ``every_prog ^noloop ((Seq Skip (Loop LN Skip LN)) : 8 loopLang$prog)``;
val _ = print_eval "ep_loop"
  ``every_prog ^noloop ((Loop LN Skip LN) : 8 loopLang$prog)``;
val _ = print_eval "ep_if"
  ``every_prog ^noloop ((If Equal 1 (Imm 0w) Skip Skip LN) : 8 loopLang$prog)``;
val _ = print_eval "ep_if_loop"
  ``every_prog ^noloop ((If Equal 1 (Imm 0w) (Loop LN Skip LN) Skip LN)
      : 8 loopLang$prog)``;
val _ = print_eval "ep_mark"
  ``every_prog ^noloop ((Mark Skip) : 8 loopLang$prog)``;
val _ = print_eval "ep_mark_loop"
  ``every_prog ^noloop ((Mark (Loop LN Skip LN)) : 8 loopLang$prog)``;
val _ = print_eval "ep_call_none"
  ``every_prog ^noloop ((Call NONE NONE [] NONE) : 8 loopLang$prog)``;
val _ = print_eval "ep_call_handler"
  ``every_prog ^noloop ((Call NONE NONE [] (SOME (0, Skip, Skip, LN)))
      : 8 loopLang$prog)``;
val _ = print_eval "ep_call_handler_fst"
  ``every_prog ^noloop ((Call NONE NONE [] (SOME (0, Loop LN Skip LN, Skip, LN)))
      : 8 loopLang$prog)``;
val _ = print_eval "ep_call_handler_snd"
  ``every_prog ^noloop ((Call NONE NONE [] (SOME (0, Skip, Loop LN Skip LN, LN)))
      : 8 loopLang$prog)``;