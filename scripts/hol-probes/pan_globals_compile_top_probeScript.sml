(* Direct original HOL EVAL of compile_top_def, including output ordering. *)
load "bossLib";
load "preamble";
load "pan_globalsTheory";
open bossLib HolKernel Parse preamble;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

val main =
  ``(<| name := «main»; inline := T; export := T; params := [(«x»,One)];
        body := panLang$Return (panLang$Var panLang$Global «g»);
        return := One |>) : 64 panLang$fun_decl``;
(* Retain the existing 64-bit sentinels and their inputs verbatim. *)
val originalMain =
  ``(panLang$Function
      <| name := «main»; inline := F; export := F; params := [];
         body := panLang$Skip; return := panLang$One |> : 64 panLang$decl)``;
val originalGlobal = ``panLang$Decl panLang$One (strlit "g")
    (panLang$Const (7w : 64 word))``;
val _ = print_eval "missing_start"
  ``pan_globals$compile_top [^originalMain] «absent»``;
val _ = print_eval "global_present"
  ``pan_globals$compile_top [^originalGlobal; ^originalMain] «main»``;
val _ = print_eval "present_start"
  ``pan_globals$compile_top [^originalMain] «main»``;
val _ = print_eval "top_missing"
  ``pan_globals$compile_top ([] : 64 panLang$decl list) «main»``;
val _ = print_eval "top_function"
  ``pan_globals$compile_top [panLang$Function ^main] «main»``;
val _ = print_eval "top_global_exception"
  ``pan_globals$compile_top
      [panLang$Function ^main; panLang$Decl One «g» (panLang$Const 7w);
       panLang$ExnDecl «E» One] «main»``;
val _ = print_eval "compile_top_probe_done" ``T``;
