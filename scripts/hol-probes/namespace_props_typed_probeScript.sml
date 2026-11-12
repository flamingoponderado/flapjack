(* Typed source declarations for namespaceProps (task 148). *)
load "preamble";
load "namespacePropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble namespacePropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="namespaceProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by namespaceProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of namespaceProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "nsLookup_nsEmpty_typed" "nsLookup_nsEmpty";
val _ = emit "nsLookupMod_nsEmpty_typed" "nsLookupMod_nsEmpty";
val _ = emit "nsLookup_nsLift_typed" "nsLookup_nsLift";
val _ = emit "nsLookupMod_nsLift_typed" "nsLookupMod_nsLift";
val _ = emit "nsDom_nsLift_typed" "nsDom_nsLift";
val _ = emit "nsDomMod_nsLift_typed" "nsDomMod_nsLift";
val _ = emit "nsDom_nsAppend_equal_typed" "nsDom_nsAppend_equal";
val _ = emit "nsAppend_nsEmpty_typed" "nsAppend_nsEmpty";
val _ = emit "nsLookup_nsBind_typed" "nsLookup_nsBind";
val _ = emit "nsAppend_assoc_typed" "nsAppend_assoc";
val _ = emit "nsAppend_to_nsBindList_typed" "nsAppend_to_nsBindList";
val _ = emit "nsAll_nsAppend_typed" "nsAll_nsAppend";
