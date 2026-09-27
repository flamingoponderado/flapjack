(* Direct HOL-EVAL probes for pan_to_crep$comp_func.
   Reference: cakeml/pancake/pan_to_crepScript.sml:337-343.
   comp_func fs eids params body =
     let vmap   = make_vmap params;
         shapes = MAP SND params;
         vmax   = size_of_shape (Comb shapes) - 1 in
     compile (mk_ctxt vmap fs vmax eids) body
   The rows exercise the parameter-driven context construction: `make_vmap`
   over `MAP FST`/`MAP SND`, the `Comb` slot bound, and the `compile` dispatch
   for concrete bodies. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
val _ = Globals.max_print_depth := 100;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "skip"
  ``pan_to_crep$comp_func FEMPTY FEMPTY [] Skip``;

val _ = print_eval "tick"
  ``pan_to_crep$comp_func FEMPTY FEMPTY [] Tick``;

val _ = print_eval "local_assign_from_param"
  ``pan_to_crep$comp_func FEMPTY FEMPTY
      [(«x», panLang$One); («y», panLang$One)]
      (Assign Local «y» (Var Local «x»))``;

val _ = print_eval "global_assign_from_param"
  ``pan_to_crep$comp_func FEMPTY FEMPTY
      [(«x», panLang$One)]
      (Assign Global «g» (Var Local «x»))``;

val _ = print_eval "primitive_params"
  ``pan_to_crep$comp_func FEMPTY FEMPTY
      [(«x», panLang$One); («y», panLang$One)]
      (Primitive «r» AddCarry [Var Local «x»; Var Local «y»])``;

val _ = print_eval "seq_tick_return"
  ``pan_to_crep$comp_func FEMPTY FEMPTY
      [(«x», panLang$One)]
      (Seq Tick (Return (Const (5w : 8 word))))``;

val _ = print_eval "combined_param_shape"
  ``pan_to_crep$comp_func FEMPTY FEMPTY
      [(«pair», panLang$Comb [panLang$One; panLang$One])]
      (Return (RStruct [Const (1w : 8 word); Const 2w]))``;

val _ = print_eval "done" ``T``;
