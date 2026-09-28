(* Direct HOL observations for source declaration routing through panSem evaluate.
   Reference: cakeml/pancake/semantics/panSemScript.sml:556-780. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val state0 = ``(s:('a,unit) panSem$state with <|
  locals := FEMPTY; globals := FEMPTY; structs := []; code := FEMPTY;
  eshapes := FEMPTY; memaddrs := {}; clock := 20; be := F;
  memory := (\a:'a word. Word 0w) |>)``;

val helper_old = ``<| name := strlit "helper"; inline := F; export := F;
  params := []; body := panLang$Return (panLang$Const 1w); return := One |>``;
val helper_new = ``<| name := strlit "helper"; inline := F; export := F;
  params := []; body := panLang$Return (panLang$Const 2w); return := One |>``;
val main = ``<| name := strlit "main"; inline := F; export := T;
  params := []; body := panLang$Call NONE (strlit "helper") [];
  return := One |>``;

val _ = print_eval "duplicate_function_front_update"
  ``case evaluate_decls ^state0 [Function ^helper_old; Function ^helper_new;
        Function ^main] of
      | SOME s' =>
          FST (evaluate (panLang$Call NONE (strlit "main") [], s'))
    | NONE => ARB``;

(* The older helper has a different formal parameter list and return shape.
   Both its code and metadata are shadowed by the later declaration. *)
val helper_old_metadata = ``<| name := strlit "helper"; inline := F; export := F;
  params := [(strlit "old_arg", One)];
  body := panLang$Return
    (panLang$Var panLang$Local (strlit "old_arg")); return := One |>``;
val helper_new_metadata = ``<| name := strlit "helper"; inline := F; export := F;
  params := []; body := panLang$Return (panLang$RStruct []);
  return := Comb [] |>``;
val main_comb = ``<| name := strlit "main"; inline := F; export := T;
  params := []; body := panLang$Call NONE (strlit "helper") [];
  return := Comb [] |>``;

val _ = print_eval "duplicate_function_front_update_changed_metadata"
  ``case evaluate_decls ^state0
        [Function ^helper_old_metadata; Function ^helper_new_metadata;
         Function ^main_comb] of
      | SOME s' =>
          FST (evaluate (panLang$Call NONE (strlit "main") [], s'))
    | NONE => ARB``;

val helper_bad_return = ``<| name := strlit "helper"; inline := F; export := F;
  params := []; body := panLang$Return (panLang$RStruct []); return := One |>``;
val main_comb_return = ``<| name := strlit "main"; inline := F; export := T;
  params := []; body := panLang$Call NONE (strlit "helper") [];
  return := Comb [] |>``;

val _ = print_eval "nested_callee_return_shape_rejected"
  ``case evaluate_decls ^state0 [Function ^helper_bad_return;
        Function ^main_comb_return] of
      | SOME s' =>
          FST (evaluate (panLang$Call NONE (strlit "main") [], s'))
    | NONE => ARB``;
