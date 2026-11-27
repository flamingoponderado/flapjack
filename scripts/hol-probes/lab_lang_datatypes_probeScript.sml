(* Typed captures for the labLang datatypes used by the backend program record. *)
load "labLangTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of labLang")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "lab_typed" "lab";
val _ = dt_label "asm_with_lab_typed" "asm_with_lab";
val _ = dt_label "asm_or_cbw_typed" "asm_or_cbw";
val _ = dt_label "line_typed" "line";
val _ = dt_label "sec_typed" "sec";
