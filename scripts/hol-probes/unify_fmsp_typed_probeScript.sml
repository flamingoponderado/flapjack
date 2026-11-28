(* Typed source declarations for the unify finite-map/sptree conversion.
   Free variables of a theorem conclusion are printed as a ∀* prefix; HOL
   stores them as implicitly universally quantified, so their order is not
   significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/src/finite_maps") ::
  !loadPath;
load "unifyTheory";
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

val thy = "unify";

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

val _ = emit "fm2sp_delete_typed" "fm2sp_delete";
val _ = emit "domain_fm2sp_typed" "domain_fm2sp";

val _ = OS.Process.exit OS.Process.success;
