(* Typed source declarations for source_letProof (task 148). *)
load "preamble";
load "source_letProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble source_letProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="source_letProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by source_letProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of source_letProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "compile_semantics_oracle_typed" "compile_semantics_oracle";
val _ = emit "compile_decs_correct_typed" "compile_decs_correct";
val _ = emit "compile_semantics_typed" "compile_semantics";
val _ = emit "evaluate_lift_lets_typed" "evaluate_lift_lets";
val _ = emit "evaluate_lift_let_typed" "evaluate_lift_let";
val _ = emit "lift_lets_is_prefix_typed" "lift_lets_is_prefix";
