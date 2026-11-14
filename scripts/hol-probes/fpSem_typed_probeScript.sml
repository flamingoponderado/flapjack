(* Typed source declarations for fpSem (task 148). *)
load "preamble";
load "fpSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble fpSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="fpSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by fpSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of fpSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "fp_bop_typed" "fp_bop";
val _ = dt_label "fp_cmp_typed" "fp_cmp";
val _ = dt_label "fp_top_typed" "fp_top";
val _ = dt_label "fp_uop_typed" "fp_uop";
val _ = emit "fp_bop_comp_def_typed" "fp_bop_comp_def";
val _ = emit "fp_cmp_def_typed" "fp_cmp_def";
val _ = emit "fp_cmp_comp_def_typed" "fp_cmp_comp_def";
val _ = emit "fp_top_comp_def_typed" "fp_top_comp_def";
val _ = emit "fp_uop_comp_def_typed" "fp_uop_comp_def";
val _ = emit "fpfma_def_typed" "fpfma_def";
