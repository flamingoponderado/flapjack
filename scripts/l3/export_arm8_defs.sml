(* Export the elaborated HOL definition theorems of the L3 ARMv8 model (arm8) and its step
   theory (arm8_step) reached from arm8_step$NextStateARM8 and the original model
   arm8$Fetch/Decode/Run/Next/Encode, in dependency order, as S-expressions
   for scripts/hol_terms_to_lean.py. Run with the pinned HOL (`hol run` from any directory);
   it writes defs.sexp in the working directory, committed as
   scripts/l3/arm8_defs.sexp.gz (gzip -9 -n). *)
val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/arm8/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/arm8/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") :: !loadPath;
load "arm8_stepTheory";
open HolKernel boolLib bossLib;
val thys = ["arm8", "arm8_step"];
fun def_for c =
  let val {Name, Thy, ...} = dest_thy_const c
  in if mem Thy thys then
       (case List.find (fn (n,_) => n = Name ^ "_def") (DB.definitions Thy) of
          SOME (n, th) => SOME (n, th)
        | NONE => (SOME (Name ^ "_def", DB.fetch Thy (Name ^ "_def")) handle _ => NONE))
     else NONE end;
fun cmp ((a,b),(c,d)) = case String.compare (a,c) of EQUAL => String.compare (b,d) | x => x;
val seen = ref (HOLset.empty cmp);
val order = ref ([] : (string * string * string * thm) list);
fun visit c =
  let val {Name, Thy, ...} = dest_thy_const c in
  if HOLset.member (!seen, (Thy, Name)) then () else
  (seen := HOLset.add (!seen, (Thy, Name));
   case def_for c of
     SOME (n, th) => (List.app visit (HolKernel.find_terms is_const (concl th));
                      order := (Thy, Name, n, th) :: !order)
   | NONE => ()) end;
val _ = visit (prim_mk_const {Thy = "arm8_step", Name = "NextStateARM8"});
val _ = List.app visit
  [prim_mk_const {Thy = "arm8", Name = "Fetch"},
   prim_mk_const {Thy = "arm8", Name = "Decode"},
   prim_mk_const {Thy = "arm8", Name = "Run"},
   prim_mk_const {Thy = "arm8", Name = "Next"},
   prim_mk_const {Thy = "arm8", Name = "Encode"}];
fun q s = "\"" ^ String.toString s ^ "\"";
fun ty t =
  if is_vartype t then "(tv " ^ q (dest_vartype t) ^ ")"
  else let val {Thy, Tyop, Args} = dest_thy_type t
       in "(ty " ^ q Thy ^ " " ^ q Tyop ^ String.concat (map (fn a => " " ^ ty a) Args) ^ ")" end;
fun tm t =
  case dest_term t of
     VAR (n, y) => "(v " ^ q n ^ " " ^ ty y ^ ")"
   | CONST {Name, Thy, Ty} => "(c " ^ q Thy ^ " " ^ q Name ^ " " ^ ty Ty ^ ")"
   | COMB (f, x) => "(a " ^ tm f ^ " " ^ tm x ^ ")"
   | LAMB (v, b) => "(l " ^ tm v ^ " " ^ tm b ^ ")";
val out = TextIO.openOut "defs.sexp";
val _ = List.app (fn (thy, name, dn, th) =>
   TextIO.output (out, "(def " ^ q thy ^ " " ^ q name ^ " " ^ q dn ^ " " ^ tm (concl th) ^ ")\n"))
   (List.rev (!order));
val _ = TextIO.closeOut out;
val _ = print ("EXPORTED " ^ Int.toString (length (!order)) ^ "\n");
