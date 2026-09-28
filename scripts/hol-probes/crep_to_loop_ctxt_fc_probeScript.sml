(* Direct HOL-EVAL observations for `crep_to_loopProof$ctxt_fc`
   (`crep_to_loopProofScript.sml:73-81`):

     ctxt_fc c cvs ns args =
       <|vars := FEMPTY |++ ZIP (ns, args);
         funcs := cvs;
         vmax := MAX_LIST args;
         target := c
         |>

   `context.vars` is `crepLang$varname |-> num` (num keys), `.funcs` is
   `crepLang$funname |-> num # num` (mlstring keys), and `.target` is the HOL
   `architecture` datatype; the exact Lean carrier is
   `Flapjack.CrepToLoopContextExact` and the port is `Flapjack.ctxtFcExact`. *)
load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "vars_zip"
  ``(ctxt_fc ARMv7 FEMPTY [1; 2] [10; 20]).vars =
      (FEMPTY |++ ZIP ([1; 2], [10; 20]))``;
val _ = print_eval "vars_zip_truncates"
  ``(ctxt_fc ARMv7 FEMPTY [1; 2; 3] [10]).vars =
      (FEMPTY |++ ZIP ([1; 2; 3], [10]))``;
val _ = print_eval "funcs_projection"
  ``(ctxt_fc ARMv7
        ((FEMPTY |+ ((«f»:mlstring), ((3:num), (2:num)))) :
           (mlstring, num # num) fmap)
        ([] : num list) ([] : num list)).funcs =
      (FEMPTY |+ ((«f»:mlstring), ((3:num), (2:num))))``;
val _ = print_eval "vmax_nonempty_list"
  ``(ctxt_fc ARMv7 FEMPTY ([] : num list) ([4; 1; 7; 3] : num list)).vmax =
      MAX_LIST ([4; 1; 7; 3] : num list)``;
val _ = print_eval "vmax_empty_list"
  ``(ctxt_fc ARMv7 FEMPTY ([] : num list) ([] : num list)).vmax = (0 : num)``;
val _ = print_eval "target_kept"
  ``(ctxt_fc ARMv7 FEMPTY ([] : num list) ([] : num list)).target = ARMv7``;
val _ = print_eval "done" ``T``;
