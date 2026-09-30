(* Direct original proof-theory code-map permutation observations. *)
load "bossLib";
load "preamble";
load "pan_globalsProofTheory";
open bossLib HolKernel Parse preamble pan_globalsProofTheory;
fun observe label q = let val th = (SIMP_CONV (srw_ss()) [FLOOKUP_fperm_code'] THENC EVAL) q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val code = ``((FEMPTY |+ («f»,([],panLang$Call NONE «f» [],One))
  |+ («g»,([],panLang$Skip,One))
  |+ («x»,([],panLang$Call NONE «g» [],One))) :
  mlstring |-> ((mlstring # panLang$shape) list # 8 panLang$prog # panLang$shape))``;
val _ = observe "swap_f" ``FLOOKUP (fperm_code «f» «g» ^code) «f»``;
val _ = observe "swap_g" ``FLOOKUP (fperm_code «f» «g» ^code) «g»``;
val _ = observe "other" ``FLOOKUP (fperm_code «f» «g» ^code) «x»``;
val _ = observe "missing" ``FLOOKUP (fperm_code «f» «g» ^code) «z»``;
val _ = observe "equal_names" ``FLOOKUP (fperm_code «f» «f» ^code) «f»``;
