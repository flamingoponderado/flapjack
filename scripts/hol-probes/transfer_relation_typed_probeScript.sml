(* Typed source declarations for the transfer relations and bounded
   quantifiers. Free variables of a theorem conclusion are printed as a ∀*
   prefix; HOL stores them as implicitly universally quantified, so their order
   is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/src/finite_maps") ::
  !loadPath;
load "quotientTheory";
load "transferTheory";
load "boolTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "∀*";
           app (fn v =>
             let val ts = type_to_string (type_of v)
                 val ts = if String.sub (ts, 0) = #":"
                          then String.extract (ts, 1, NONE) else ts
             in print "("; print (#1 (dest_var v));
                print " :"; print ts; print ") " end) fvs;
           print ". ");
     app (fn h => (print_term h; print " ==> ")) (hyp th);
     print_term (concl th); print "\n")
  end;

fun emitIn label sourceTheory name =
  case DB.lookup {Thy = sourceTheory, Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in " ^ sourceTheory ^ ">\n");

val _ = emitIn "FUN_REL_typed" "quotient" "FUN_REL";
val _ = emitIn "total_def_typed" "transfer" "total_def";
val _ = emitIn "surj_def_typed" "transfer" "surj_def";
val _ = emitIn "bitotal_def_typed" "transfer" "bitotal_def";
val _ = emitIn "RES_FORALL_DEF_typed" "bool" "RES_FORALL_DEF";
val _ = emitIn "RES_EXISTS_DEF_typed" "bool" "RES_EXISTS_DEF";

val _ = OS.Process.exit OS.Process.success;
