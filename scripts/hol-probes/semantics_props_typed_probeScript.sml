(* Typed source declarations for semanticsProps (task 148). *)
load "preamble";
load "semanticsPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticsPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="semanticsProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by semanticsProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of semanticsProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "extend_with_resource_limit_def_typed" "extend_with_resource_limit_def";
val _ = emit "extend_with_resource_limit_not_fail_typed" "extend_with_resource_limit_not_fail";
val _ = emit "implements_def_typed" "implements_def";
val _ = emit "implements_trans_typed" "implements_trans";
val _ = emit "evaluate_prog_events_determ_typed" "evaluate_prog_events_determ";
val _ = emit "evaluate_prog_io_events_chain_typed" "evaluate_prog_io_events_chain";
val _ = emit "semantics_prog_total_typed" "semantics_prog_total";
val _ = emit "semantics_prog_deterministic_typed" "semantics_prog_deterministic";
