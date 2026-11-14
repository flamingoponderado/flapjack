(* Typed source declarations for ffi (task 148). *)
load "preamble";
load "ffiTheory";
open HolKernel Parse boolLib bossLib;
open preamble ffiTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="ffi",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by ffi")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of ffi")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "behaviour_typed" "behaviour";
val _ = dt_label "ffiname_typed" "ffiname";
val _ = dt_label "ffi_outcome_typed" "ffi_outcome";
val _ = dt_label "ffi_result_typed" "ffi_result";
val _ = dt_label "ffi_state_typed" "ffi_state";
val _ = dt_label "final_event_typed" "final_event";
val _ = dt_label "io_event_typed" "io_event";
val _ = dt_label "oracle_result_typed" "oracle_result";
val _ = dt_label "outcome_typed" "outcome";
val _ = dt_label "shmem_op_typed" "shmem_op";
val _ = emit "call_FFI_def_typed" "call_FFI_def";
val _ = emit "initial_ffi_state_def_typed" "initial_ffi_state_def";
