(* Export the pinned translated 64-bit CakeML compiler using the same
   conversion as unverified/sexpr-bootstrap/x64/64/x64SexprScript.sml.
   CAKE_SEXPR_OUTPUT points outside the read-only reference checkout. *)
load "compiler64ProgTheory";
load "astToSexprLib";
open HolKernel Parse boolLib bossLib astToSexprLib;

val output = case OS.Process.getEnv "CAKE_SEXPR_OUTPUT" of
    SOME path => path
  | NONE => raise Fail "CAKE_SEXPR_OUTPUT must name the output file";

val _ = compiler64ProgTheory.compiler64_prog_def
          |> CONV_RULE (RAND_CONV EVAL)
          |> concl
          |> rhs
          |> write_ast_to_file output;
val _ = print ("wrote translated compiler to " ^ output ^ "\n");
