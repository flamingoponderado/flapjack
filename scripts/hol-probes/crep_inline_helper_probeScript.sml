(* Direct HOL-EVAL observations for the helper functions used by
   `inline_prog` (`cakeml/pancake/crep_inlineScript.sml`), so the Lean
   counterparts (`crepVarProgHOLExact`, `crepVmaxProgHOLExact`,
   `crepTransformEoc`, `crepTransformBranch`, `crepInlineTail`,
   `crepArgLoad`, `crepInlineNontail`, `crepUnreachElim`) can be compared
   clause for clause against the original definitions.

   Rows are boolean projections (helper output equals an explicit expected
   term) so each prints on a single line.

   References (crep_inlineScript.sml):
     :8-38 var_prog/vmax_prog
     :59   arg_load
     :86   unreach_elim
     :137  transform_eoc
     :155  transform_branch
     :168  inline_tail
     :193  inline_nontail *)

load "bossLib";
load "preamble";
load "crep_inlineTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_inlineTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val body = ``(Dec 1 (Const (1w:8 word)) Skip) : 8 crepLang$prog``;
val p =
  ``(Seq (Dec 1 (Const (1w:8 word))
                 (crepLang$Return ([(crepLang$Var 2)] : 8 crepLang$exp list)))
         Skip) : 8 crepLang$prog``;

val var_case =
  ``(Seq
       (Call (SOME ([12], SOME ((3w:8 word), Assign 13 (Var 14))))
         «f» [Var 10; Var 11])
       (ExtCall «g» 20 21 22 23)) : 8 crepLang$prog``;
val _ = print_eval "var_prog_call_handler_extcall"
  ``var_prog ^var_case = [10; 11; 12; 13; 14; 20; 21; 22; 23]``;
val _ = print_eval "vmax_prog_call_handler_extcall"
  ``vmax_prog ^var_case = 23``;
val _ = print_eval "var_prog_skip_empty"
  ``var_prog (Skip : 8 crepLang$prog) = []``;
val _ = print_eval "vmax_prog_skip_zero"
  ``vmax_prog (Skip : 8 crepLang$prog) = 0``;
val _ = print_eval "var_prog_storeglob_ignores_address"
  ``var_prog (StoreGlob 4w (Var 8) : 8 crepLang$prog) = [8]``;

val _ = print_eval "eoc_p"
  ``(transform_eoc [10] ^p =
      (Seq (Dec 1 (Const 1w) (Seq (Assign 10 (Var 2)) Skip)) Skip) :
        8 crepLang$prog)``;
val _ = print_eval "branch_p"
  ``(transform_branch 0 [10] ^p =
      (Seq (Dec 1 (Const 1w)
             (Seq (Seq (Assign 10 (Var 2)) Skip) (Break 0)))
         Skip) : 8 crepLang$prog)``;
val _ = print_eval "tail_p"
  ``(inline_tail ^p =
      (Seq Tick (Seq (Dec 1 (Const 1w) (Return [Var 2])) Skip)) :
        8 crepLang$prog)``;
val _ = print_eval "argload_p"
  ``(arg_load [20] [Const (5w:8 word)] [7] ^body =
      (Dec 20 (Const 5w) (Dec 7 (Var 20) (Dec 1 (Const 1w) Skip))) :
        8 crepLang$prog)``;
val _ = print_eval "nontail_p"
  ``(inline_nontail ^body [10] [11] [20] [Const (5w:8 word)] [7] =
      (Dec 11 (Const 0w)
         (Seq (Dec 20 (Const 5w) (Dec 7 (Var 20) (Dec 1 (Const 1w) Skip)))
            (Seq (Assign 10 (Var 11)) Skip))) : 8 crepLang$prog)``;
val _ = print_eval "unreach_p"
  ``(FST (unreach_elim ^p) =
      (Dec 1 (Const 1w) (Return [Var 2])) : 8 crepLang$prog)``;
