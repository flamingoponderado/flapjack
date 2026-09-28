(* Direct HOL-EVAL observations of loopProps$comp_syntax_ok_def clauses.
   The If clause's set-extension condition is HOL's classical existential
   [EXISTS ns. nl = FOLDL (\sp n. insert n () sp) l ns]. HOL EVAL can reduce
   the FOLDL for a concrete ns list but does not search over List num, so the
   If rows below print the residual existential rather than a T/F; this is
   recorded explicitly and not reported as a computed result.  The matching
   If case is additionally proved by instantiating that witness. *)
load "bossLib";
load "preamble";
load "loopPropsTheory";
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

fun print_thm label th =
  let
    val th = th
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val l8 = ``insert 8 () LN``;

val _ = print_eval "comp_skip"
  ``comp_syntax_ok ^l8 (loopLang$Skip : 8 loopLang$prog)``;
val _ = print_eval "comp_assign"
  ``comp_syntax_ok ^l8 (loopLang$Assign 4 (loopLang$Const (0w : 8 word)) : 8 loopLang$prog)``;
val _ = print_eval "comp_locvalue"
  ``comp_syntax_ok ^l8 (loopLang$LocValue 3 4 : 8 loopLang$prog)``;
val _ = print_eval "comp_load32"
  ``comp_syntax_ok ^l8 (loopLang$Load32 5 6 : 8 loopLang$prog)``;
val _ = print_eval "comp_loadbyte"
  ``comp_syntax_ok ^l8 (loopLang$LoadByte 7 9 : 8 loopLang$prog)``;
val _ = print_eval "comp_break"
  ``comp_syntax_ok ^l8 (loopLang$Break 11 : 8 loopLang$prog)``;
val _ = print_eval "comp_arith"
  ``comp_syntax_ok ^l8 (loopLang$Arith (loopLang$LDiv 7 8 9) : 8 loopLang$prog)``;
val _ = print_eval "comp_seq"
  ``comp_syntax_ok ^l8
      (loopLang$Seq (loopLang$LocValue 1 3)
                    (loopLang$Assign 1 (loopLang$Var 1)) : 8 loopLang$prog)``;
val _ = print_eval "comp_seq_cutset"
  ``comp_syntax_ok ^l8
      (loopLang$Seq (loopLang$LocValue 1 3)
                    (loopLang$Loop (insert 1 () ^l8) loopLang$Skip
                                   (insert 1 () ^l8)) : 8 loopLang$prog)``;
val _ = print_eval "comp_loop_ok"
  ``comp_syntax_ok ^l8 (loopLang$Loop ^l8 loopLang$Skip ^l8 : 8 loopLang$prog)``;
val _ = print_eval "comp_loop_bad"
  ``comp_syntax_ok ^l8
      (loopLang$Loop ^l8 loopLang$Skip (insert 9 () ^l8) : 8 loopLang$prog)``;
val _ = print_eval "comp_store_fallback"
  ``comp_syntax_ok ^l8
      (loopLang$Store (loopLang$Const (0w : 8 word)) 4 : 8 loopLang$prog)``;
val _ = print_eval "comp_raise_fallback"
  ``comp_syntax_ok ^l8 (loopLang$Raise 0 : 8 loopLang$prog)``;
val _ = print_eval "comp_tick_fallback"
  ``comp_syntax_ok ^l8 (loopLang$Tick : 8 loopLang$prog)``;
val _ = print_eval "comp_if_unreduced"
  ``comp_syntax_ok ^l8
      (loopLang$If asm$Equal 1 (asm$Imm 0w) loopLang$Skip loopLang$Skip
        (FOLDL (\sp n. insert n () sp) ^l8 [1;2]) : 8 loopLang$prog)``;
val _ = print_eval "comp_if_nonmatching"
  ``comp_syntax_ok ^l8
      (loopLang$If asm$Equal 1 (asm$Imm 0w) loopLang$Skip loopLang$Skip
        (insert 5 () LN) : 8 loopLang$prog)``;

(* The matching If case is decidable in HOL by exhibiting the witness list,
   but not by EVAL alone.  The following proves the source T result from the
   EVAL normal form by instantiating the residual existential, so the row is
   recorded without pretending EVAL computed it. *)
val if_unreduced = EVAL
  ``comp_syntax_ok ^l8
      (loopLang$If asm$Equal 1 (asm$Imm 0w) loopLang$Skip loopLang$Skip
        (FOLDL (\sp n. insert n () sp) ^l8 [1;2]) : 8 loopLang$prog)``;
val if_exist_thm = prove(rconc if_unreduced,
  qexists_tac `[1;2]` >> EVAL_TAC);
val if_matching_thm = TRANS if_unreduced (EQT_INTRO if_exist_thm);
val _ = print_thm "comp_if_witness_ok" if_matching_thm;
val _ = print_thm "comp_if_witness_ok" if_matching_thm;
