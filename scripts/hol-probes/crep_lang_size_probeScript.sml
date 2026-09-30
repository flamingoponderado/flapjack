(* Direct HOL oracle for the *generated* datatype size functions of crepLang.

   HOL's `Datatype` command generates `exp_size`/`prog_size` and their
   auxiliaries for cakeml/pancake/crepLangScript.sml.  They are not textual
   source declarations, so `scripts/check-hol-refs.py` cannot resolve them and
   the Lean transcriptions cannot carry an `@[hol]` tag.  The crep_inline
   theorem `unreach_elim_prog_size` (crep_inlineProofScript.sml:1730) is stated
   over `prog_size`, so its exact equations are printed here from the real
   CakeML `crepLangTheory`.  Regenerate with:

     CAKEML=<built CakeML checkout> \
       HOL_PROBE_ONLY=crep_lang_size_probeScript.sml scripts/hol-probes/regenerate.sh *)

load "bossLib";
load "preamble";
load "crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_thm label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  );

val () = print_thm "exp_size_def" (fetch "crepLang" "exp_size_def");
val () = print_thm "prog_size_def" (fetch "crepLang" "prog_size_def");

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val p_seq =
  ``crepLang$Seq (crepLang$Assign 1 (crepLang$Const (7w : 8 word)))
      (crepLang$Return [crepLang$Var 2])``;
val p_call =
  ``crepLang$Call (SOME ([1], SOME (3w : 8 word, crepLang$Break 0))) (strlit "f")
      [crepLang$Var 1]``;
val p_dec =
  ``crepLang$Dec 4 (crepLang$Op asm$Add [crepLang$Var 1; crepLang$Const (2w : 8 word)])
      (crepLang$While (crepLang$Var 4) crepLang$Tick)``;
val p_ext = ``(crepLang$ExtCall (strlit "g") 1 2 3 4 : 8 crepLang$prog)``;
val p_raise = ``(crepLang$Raise (5w : 8 word) : 8 crepLang$prog)``;

val () = print_eval "prog_size_seq" ``prog_size (K 0) ^p_seq``;
val () = print_eval "prog_size_call" ``prog_size (K 0) ^p_call``;
val () = print_eval "prog_size_dec" ``prog_size (K 0) ^p_dec``;
val () = print_eval "prog_size_ext" ``prog_size (K 0) ^p_ext``;
val () = print_eval "prog_size_raise" ``prog_size (K 0) ^p_raise``;
