(* Direct original HOL compile_def cases at pan_structsScript.sml157-210.
   Regenerate with HOL_PROBE_ONLY=pan_structs_compile_prog_probeScript.sml
   scripts/hol-probes/regenerate.sh. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
open bossLib HolKernel Parse preamble;
val ctxt =
  ``<| structs := [(«Pair», [(«left», One); («right», Comb [One; One])])];
       locals := []; globals := [] |>``;
fun print_eval label q =
  let val th = EVAL q
  in print (label ^ "="); print_term (rconc th); print "\n" end;
val _ = print_eval "dec"
  ``pan_structs$compile ^ctxt
      (Dec «v» (Named «Pair»)
        (NStruct «Pair» [(«left», Const (1w : 8 word)); («right», Const 2w)])
        (Return (NField «right» (Var Local «v»))))``;
val _ = print_eval "deccall"
  ``pan_structs$compile ^ctxt
      (DecCall «v» (Named «Pair») «f» ([] : 8 word exp list)
        (Return (NField «right» (Var Local «v»))))``;
val _ = print_eval "handler"
  ``pan_structs$compile ^ctxt
      (Call (SOME (NONE, SOME («E», «v», Return (NField «right» (NStruct «Pair» [])))))
        «f» ([] : 8 word exp list))``;
val _ = print_eval "callnone"
  ``pan_structs$compile ^ctxt (Call NONE «f» ([] : 8 word exp list))``;
val _ = print_eval "callnohandler"
  ``pan_structs$compile ^ctxt
      (Call (SOME (SOME (Local, «v»), NONE)) «f» ([] : 8 word exp list))``;
val _ = print_eval "fallback"
  ``pan_structs$compile ^ctxt (Tick : 8 word prog)``;
