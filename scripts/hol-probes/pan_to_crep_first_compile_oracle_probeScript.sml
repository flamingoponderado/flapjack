(* Direct HOL-EVAL oracle rows for pan_to_crepProof first_compile_prog_all_distinct:
   ALL_DISTINCT of the source function names and of the compiled names, for a
   distinct-name program (positive) and a duplicate-name program (negative).
   Reference: cakeml/pancake/proofs/pan_to_crepProofScript.sml:4556-4568. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "distinct_names"
  ``let p = [panLang$Function
         <| name := «leaf»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (7w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «mid»; inline := T; export := F;
            params := []; body := panLang$Call NONE «leaf» [];
            return := panLang$One |>;
       panLang$Function
         <| name := «main»; inline := F; export := T;
            params := []; body := panLang$Call NONE «mid» [];
            return := panLang$One |>] in
    (ALL_DISTINCT (MAP FST (panLang$functions p)),
     ALL_DISTINCT (MAP FST (pan_to_crep$compile_prog p)))``;

val _ = print_eval "duplicate_names"
  ``let p = [panLang$Function
         <| name := «id»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (7w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «id»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (9w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «main»; inline := F; export := T;
            params := []; body := panLang$Call NONE «id» [];
            return := panLang$One |>] in
    (ALL_DISTINCT (MAP FST (panLang$functions p)),
     ALL_DISTINCT (MAP FST (pan_to_crep$compile_prog p)))``;
